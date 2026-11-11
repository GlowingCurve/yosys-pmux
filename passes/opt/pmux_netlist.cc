#include "passes/opt/pmux_netlist.h"

#include <algorithm>

YOSYS_NAMESPACE_BEGIN

PmuxNetlist::PmuxNetlist(Module *module, Design *design) : module_(module), design_(design)
{
	log_assert(module_ && design_ && module_->design == design_);
	sigmap_.set(module_);
	types_.setup();
	for (auto wire : module_->wires()) {
		bool keep = wire->get_bool_attribute(ID::keep);
		if (!wire->port_input && !wire->port_output && !keep)
			continue;
		for (auto bit : sigmap_(wire)) {
			auto &info = bits_[bit];
			info.inputs += wire->port_input;
			info.outputs += wire->port_output;
			info.keeps += keep;
			update_protection(bit, info);
		}
	}
	for (auto cell : module_->cells())
		register_cell(cell);
	revision_ = 0;
}

bool PmuxNetlist::cell_evaluable(IdString type) const
{
	return types_.cell_evaluable(type);
}

RTLIL::PortDir PmuxNetlist::cell_port_dir(IdString type, IdString port) const
{
	return types_.cell_port_dir(type, port);
}

bool PmuxNetlist::cell_input(IdString type, IdString port) const
{
	return types_.cell_input(type, port);
}

bool PmuxNetlist::cell_output(IdString type, IdString port) const
{
	return types_.cell_output(type, port);
}

const SigSpec &PmuxNetlist::port(Cell *cell, IdString name) const
{
	log_assert(cell && cells_.count(cell) && cell->hasPort(name));
	auto &cached = ports_[{cell, name}];
	if (!cached)
		cached = std::make_unique<CachedPort>(CachedPort{sigmap_(cell->getPort(name)), alias_revision_});
	else if (cached->alias_revision != alias_revision_) {
		cached->signal = sigmap_(cell->getPort(name));
		cached->alias_revision = alias_revision_;
	}
	return cached->signal;
}

bool PmuxNetlist::operand_signed(Cell *cell, IdString name) const
{
	log_assert(name.in(ID::A, ID::B));
	auto param = name == ID::A ? ID::A_SIGNED : ID::B_SIGNED;
	if (cell->type.in(ID($eq), ID($ne), ID($eqx), ID($nex)))
		return !cell->getPort(name).empty() && cell->getParam(ID::A_SIGNED).as_bool() && cell->getParam(ID::B_SIGNED).as_bool();
	return cell->hasParam(param) && cell->getParam(param).as_bool();
}

SigBit PmuxNetlist::operand(Cell *cell, IdString name, int offset) const
{
	log_assert(offset >= 0);
	const auto &signal = port(cell, name);
	if (offset < GetSize(signal))
		return signal[offset];
	if (!operand_signed(cell, name))
		return State::S0;
	return signal.empty() ? SigBit(State::Sx) : signal.back();
}

SigSpec PmuxNetlist::extended(Cell *cell, IdString name, int width) const
{
	log_assert(width >= 0);
	auto signal = port(cell, name);
	signal.extend_u0(width, operand_signed(cell, name));
	return signal;
}

const PmuxNetlist::BitInfo *PmuxNetlist::bit_info(SigBit bit) const
{
	auto found = bits_.find(sigmap_(bit));
	return found == bits_.end() ? nullptr : &found->second;
}

const PmuxNetlist::Driver *PmuxNetlist::source(SigBit bit) const
{
	static const Driver module_input{nullptr, {}, 0};
	bit = sigmap_(bit);
	if (!bit.wire)
		return nullptr;
	auto found = bits_.find(bit);
	if (found == bits_.end() || found->second.uncertain())
		return nullptr;
	const auto &info = found->second;
	if (!info.drivers.empty())
		return &info.drivers.front();
	return info.inputs ? &module_input : nullptr;
}

Cell *PmuxNetlist::driver(SigBit bit) const
{
	auto found = source(bit);
	return found ? found->cell : nullptr;
}

bool PmuxNetlist::kept(SigBit bit) const
{
	auto info = bit_info(bit);
	return info && info->keeps != 0;
}

bool PmuxNetlist::protected_bit(SigBit bit) const
{
	return protected_bits_.count(sigmap_(bit));
}

bool PmuxNetlist::uncertain(SigBit bit) const
{
	bit = sigmap_(bit);
	auto found = bits_.find(bit);
	if (found == bits_.end())
		return false;
	const auto &info = found->second;
	return info.uncertain() || (!bit.wire && (info.inputs != 0 || !info.drivers.empty()));
}

bool PmuxNetlist::uncertain_cell(Cell *cell) const
{
	log_assert(cell && cells_.count(cell));
	return cells_.at(cell).uncertain_ports != 0;
}

bool PmuxNetlist::selected(Cell *cell) const
{
	log_assert(cell);
	auto found = cells_.find(cell);
	return found != cells_.end() && found->second.selected;
}

bool PmuxNetlist::editable_cell(Cell *cell) const
{
	return selected(cell) && !cells_.at(cell).keep && !uncertain_cell(cell);
}

bool PmuxNetlist::editable_output(Cell *cell, IdString name, int offset, SigBit bit) const
{
	auto found = source(bit);
	return found && found->cell == cell && found->port == name && found->offset == offset && !kept(bit);
}

bool PmuxNetlist::editable(Cell *cell, IdString name) const
{
	if (!editable_cell(cell) || !cell->hasPort(name) || cell_port_dir(cell->type, name) != RTLIL::PD_OUTPUT)
		return false;
	const auto &signal = port(cell, name);
	for (int i = 0; i < GetSize(signal); i++)
		if (!editable_output(cell, name, i, signal[i]))
			return false;
	return !signal.empty();
}

bool PmuxNetlist::editable_bit(Cell *cell, IdString name, int offset) const
{
	log_assert(cell && cell->hasPort(name) && offset >= 0 && offset < GetSize(cell->getPort(name)));
	return editable_cell(cell) && editable_output(cell, name, offset, port(cell, name)[offset]);
}

void PmuxNetlist::update_protection(SigBit bit, const BitInfo &info)
{
	if (info.protected_bit())
		protected_bits_.insert(bit);
	else
		protected_bits_.erase(bit);
}

void PmuxNetlist::index_users(Cell *cell, IdString name, const SigSpec &signal, int delta) const
{
	for (int i = 0; i < GetSize(signal); i++) {
		auto bit = sigmap_(signal[i]);
		if (!bit.wire)
			continue;
		if (delta > 0) {
			users_[bit].push_back({cell, name, i});
			continue;
		}
		auto &users = users_.at(bit);
		auto found = std::find_if(users.begin(), users.end(), [&](const User &user) {
			return user.cell == cell && user.port == name && user.offset == i;
		});
		log_assert(found != users.end());
		users.erase(found);
		if (users.empty())
			users_.erase(bit);
	}
}

void PmuxNetlist::ensure_users() const
{
	if (users_ready_)
		return;
	for (const auto &[cell, info] : cells_)
		for (const auto &[name, signal] : cell->connections())
			if (cell_port_dir(cell->type, name) != RTLIL::PD_OUTPUT)
				index_users(cell, name, signal, 1);
	users_ready_ = true;
}

const std::vector<PmuxNetlist::User> &PmuxNetlist::users(SigBit bit) const
{
	static const std::vector<User> empty;
	bit = sigmap_(bit);
	if (!bit.wire)
		return empty;
	ensure_users();
	auto found = users_.find(bit);
	return found == users_.end() ? empty : found->second;
}

void PmuxNetlist::index_port(Cell *cell, IdString name, const SigSpec &signal, int delta)
{
	auto &cell_info = cells_.at(cell);
	auto direction = cell_port_dir(cell->type, name);
	bool unknown = direction == RTLIL::PD_UNKNOWN || direction == RTLIL::PD_INOUT;
	bool output = direction == RTLIL::PD_OUTPUT || direction == RTLIL::PD_INOUT;
	cell_info.uncertain_ports += unknown ? delta : 0;
	if (output || unknown || cell_info.keep) {
		for (int i = 0; i < GetSize(signal); i++) {
			auto bit = sigmap_(signal[i]);
			auto &info = delta > 0 ? bits_[bit] : bits_.at(bit);
			info.keeps += cell_info.keep ? delta : 0;
			info.uncertain_ports += unknown ? delta : 0;
			if (output && delta > 0) {
				info.drivers.push_back({cell, name, i});
			} else if (output) {
				auto found = std::find_if(info.drivers.begin(), info.drivers.end(), [&](const Driver &driver) {
					return driver.cell == cell && driver.port == name && driver.offset == i;
				});
				log_assert(found != info.drivers.end());
				info.drivers.erase(found);
			}
			update_protection(bit, info);
			if (info.empty())
				bits_.erase(bit);
		}
	}
	if (users_ready_ && direction != RTLIL::PD_OUTPUT)
		index_users(cell, name, signal, delta);
}

void PmuxNetlist::register_cell(Cell *cell)
{
	log_assert(cell && cell->module == module_ && !cells_.count(cell));
	if (!types_.cell_known(cell->type) && registered_types_.insert(cell->type).second)
		if (auto definition = design_->module(cell->type))
			types_.setup_module(definition);
	cells_.emplace(cell, CellInfo{design_->selected(module_, cell), cell->get_bool_attribute(ID::keep)});
	for (const auto &[name, signal] : cell->connections())
		index_port(cell, name, signal, 1);
	revision_++;
}

void PmuxNetlist::forget_cell(Cell *cell)
{
	log_assert(cell && cells_.count(cell));
	for (const auto &[name, signal] : cell->connections()) {
		index_port(cell, name, signal, -1);
		ports_.erase({cell, name});
	}
	cells_.erase(cell);
	revision_++;
}

void PmuxNetlist::set_port(Cell *cell, IdString name, const SigSpec &signal)
{
	log_assert(cell && cells_.count(cell));
	if (cell->hasPort(name)) {
		const auto &old = cell->getPort(name);
		if (old == signal)
			return;
		index_port(cell, name, old, -1);
	}
	cell->setPort(name, signal);
	ports_.erase({cell, name});
	index_port(cell, name, cell->getPort(name), 1);
	revision_++;
}

void PmuxNetlist::merge_bits(SigBit from, SigBit to)
{
	auto source = bits_.find(from);
	if (source != bits_.end()) {
		auto old = std::move(source->second);
		bits_.erase(source);
		protected_bits_.erase(from);
		auto &info = bits_[to];
		info.inputs += old.inputs;
		info.outputs += old.outputs;
		info.keeps += old.keeps;
		info.uncertain_ports += old.uncertain_ports;
		if (info.drivers.empty())
			info.drivers = std::move(old.drivers);
		else
			info.drivers.insert(info.drivers.end(), old.drivers.begin(), old.drivers.end());
		update_protection(to, info);
	}
	auto consumers = users_.find(from);
	if (consumers == users_.end())
		return;
	auto old = std::move(consumers->second);
	users_.erase(consumers);
	if (!to.wire)
		return;
	auto &users = users_[to];
	if (users.empty())
		users = std::move(old);
	else
		users.insert(users.end(), old.begin(), old.end());
}

void PmuxNetlist::connect(const SigSpec &lhs, const SigSpec &rhs)
{
	log_assert(GetSize(lhs) == GetSize(rhs));
	module_->connect(lhs, rhs);
	bool changed = false;
	for (int i = 0; i < GetSize(lhs); i++) {
		if (!lhs[i].wire)
			continue;
		auto a = sigmap_(lhs[i]), b = sigmap_(rhs[i]);
		if (a == b || (!a.wire && !b.wire))
			continue;
		sigmap_.add(a, b);
		auto representative = sigmap_(a);
		log_assert(representative == a || representative == b);
		merge_bits(representative == a ? b : a, representative);
		changed = true;
	}
	if (changed) {
		alias_revision_++;
		revision_++;
	}
}

bool PmuxNetlist::combinational_inputs(SigBit bit, SigSpec &inputs) const
{
	inputs = {};
	bit = sigmap_(bit);
	if (!bit.wire)
		return !uncertain(bit);
	auto source = this->source(bit);
	if (!source)
		return false;
	auto cell = source->cell;
	if (!cell || StaticCellTypes::categories.is_ff(cell->type))
		return true;
	auto type = cell->type;
	if (uncertain_cell(cell) || (!cell_evaluable(type) && !StaticCellTypes::categories.is_tristate(type)))
		return false;
	int offset = source->offset;
	if (type.in(ID($buf), ID($pos), ID($not))) {
		inputs.append(operand(cell, ID::A, offset));
	} else if (type.in(ID($and), ID($or), ID($xor), ID($xnor), ID($bweqx))) {
		inputs.append(operand(cell, ID::A, offset));
		inputs.append(operand(cell, ID::B, offset));
	} else if (type.in(ID($mux), ID($pmux), ID($bwmux), ID($_MUX_))) {
		const auto &a = port(cell, ID::A), &b = port(cell, ID::B), &s = port(cell, ID::S);
		int width = GetSize(a);
		log_assert(offset < width);
		if (type == ID($pmux)) {
			log_assert(GetSize(b) == width * GetSize(s));
			inputs.append(a[offset]);
			for (int i = 0; i < GetSize(s); i++)
				inputs.append(b[i * width + offset]);
			inputs.append(s);
		} else {
			log_assert(GetSize(b) == width && GetSize(s) == (type == ID($bwmux) ? width : 1));
			inputs.append(a[offset]);
			inputs.append(b[offset]);
			inputs.append(s[type == ID($bwmux) ? offset : 0]);
		}
	} else if (type.in(ID($tribuf), ID($_TBUF_))) {
		const auto &a = port(cell, ID::A), &enable = port(cell, type == ID($tribuf) ? ID::EN : ID::E);
		log_assert(offset < GetSize(a) && GetSize(enable) == 1);
		inputs.append(a[offset]);
		inputs.append(enable);
	} else if (type == ID($slice)) {
		const auto &a = port(cell, ID::A);
		int index = offset + cell->getParam(ID::OFFSET).as_int();
		log_assert(index >= 0 && index < GetSize(a));
		inputs.append(a[index]);
	} else if (type == ID($concat)) {
		const auto &a = port(cell, ID::A), &b = port(cell, ID::B);
		log_assert(offset < GetSize(a) + GetSize(b));
		inputs.append(offset < GetSize(a) ? a[offset] : b[offset - GetSize(a)]);
	} else {
		for (const auto &[name, signal] : cell->connections())
			if (cell_input(type, name))
				inputs.append(port(cell, name));
	}
	return true;
}

PmuxNetlist::Dependencies::Dependencies(const PmuxNetlist &netlist, const pool<SigBit> &targets, int &work,
		bool track_high_z, pool<SigBit> *references)
	: netlist_(netlist), work_(work), track_high_z_(track_high_z), references_(references), revision_(netlist.revision())
{
	log_assert(!track_high_z || references == nullptr);
	for (auto target : targets)
		targets_.insert(netlist_.sigmap_(target));
}

bool PmuxNetlist::Dependencies::high_z(SigBit bit) const
{
	log_assert(track_high_z_ && revision_ == netlist_.revision());
	bit = netlist_.sigmap_(bit);
	if (!bit.wire)
		return bit == RTLIL::State::Sz;
	auto found = state_.find(bit);
	log_assert(found != state_.end() && (found->second == State::Logic || found->second == State::HighZ));
	return found->second == State::HighZ;
}

bool PmuxNetlist::Dependencies::output_high_z(const Driver &source, const SigSpec &inputs) const
{
	auto cell = source.cell;
	auto type = cell->type;
	if (type == ID($lut)) {
		const auto &table = cell->parameters.at(ID::LUT);
		int width = cell->getParam(ID::WIDTH).as_int();
		log_assert(width >= 0 && source.offset == 0);
		for (int i = 0; i < GetSize(table) && (width >= 31 || (i >> width) == 0); i++)
			if (table[i] == RTLIL::State::Sz)
				return true;
		return false;
	}
	if (type.in(ID($not), ID($and), ID($or), ID($xor), ID($xnor), ID($bweqx), ID($logic_not), ID($logic_and), ID($logic_or),
		ID($reduce_bool), ID($reduce_or), ID($reduce_and), ID($reduce_xor), ID($reduce_xnor),
		ID($eq), ID($ne), ID($eqx), ID($nex), ID($lt), ID($le), ID($gt), ID($ge), ID($sop),
		ID($_NOT_), ID($_AND_), ID($_OR_), ID($_XOR_), ID($_XNOR_), ID($_NAND_), ID($_NOR_), ID($_ANDNOT_), ID($_ORNOT_)))
		return false;
	if (type.in(ID($mux), ID($bwmux), ID($_MUX_))) {
		auto select = inputs[2];
		return (select != RTLIL::State::S1 && high_z(inputs[0])) || (select != RTLIL::State::S0 && high_z(inputs[1]));
	}
	if (type == ID($pmux)) {
		int width = GetSize(netlist_.port(cell, ID::S));
		int selected = -1;
		for (int i = 0; i < width; i++)
			if (inputs[1 + width + i] == RTLIL::State::S1) {
				if (selected >= 0)
					return false;
				selected = i;
			}
		if (selected >= 0)
			return high_z(inputs[1 + selected]);
		if (high_z(inputs[0]))
			return true;
		for (int i = 0; i < width; i++)
			if (inputs[1 + width + i] != RTLIL::State::S0 && high_z(inputs[1 + i]))
				return true;
		return false;
	}
	if (type.in(ID($tribuf), ID($_TBUF_)))
		return inputs[1] != RTLIL::State::S1 || high_z(inputs[0]);
	for (auto bit : inputs)
		if (high_z(bit))
			return true;
	return false;
}

bool PmuxNetlist::Dependencies::visit(SigBit bit)
{
	log_assert(revision_ == netlist_.revision());
	return visit(bit, 0);
}

bool PmuxNetlist::Dependencies::visit(SigBit bit, int depth)
{
	if (--work_ < 0 || depth > 128)
		return false;
	bit = netlist_.sigmap_(bit);
	if (targets_.count(bit)) {
		if (!references_)
			return false;
		references_->insert(bit);
		return true;
	}
	if (!bit.wire)
		return !netlist_.uncertain(bit);
	auto found = state_.find(bit);
	if (found != state_.end())
		return found->second == State::Logic || found->second == State::HighZ;
	SigSpec inputs;
	if (!netlist_.combinational_inputs(bit, inputs)) {
		state_[bit] = State::Unresolved;
		return false;
	}
	state_[bit] = State::Active;
	for (auto input : inputs)
		if (!visit(input, depth + 1)) {
			state_[bit] = State::Unresolved;
			return false;
		}
	auto source = netlist_.source(bit);
	log_assert(source);
	bool high = false;
	if (track_high_z_ && source->cell && !StaticCellTypes::categories.is_ff(source->cell->type)) {
		if (source->cell->type == ID($lut)) {
			work_ -= GetSize(source->cell->parameters.at(ID::LUT));
			if (work_ < 0) {
				state_[bit] = State::Unresolved;
				return false;
			}
		}
		high = output_high_z(*source, inputs);
	}
	state_[bit] = high ? State::HighZ : State::Logic;
	return true;
}

bool PmuxNetlist::independent(const pool<SigBit> &leaves, const pool<SigBit> &targets, int &work) const
{
	Dependencies dependencies(*this, targets, work);
	for (auto bit : leaves)
		if (!dependencies.visit(bit))
			return false;
	return true;
}

bool PmuxNetlist::private_signal(const SigSpec &signal, const pool<Cell *> &allowed) const
{
	for (auto bit : signal) {
		if (!driver(bit) || protected_bit(bit))
			return false;
		for (const auto &user : users(bit))
			if (!allowed.count(user.cell))
				return false;
	}
	return true;
}

pool<Cell *> PmuxNetlist::private_cells(const pool<Cell *> &region, const pool<Cell *> &roots,
		const pool<SigBit> &targets, const pool<SigBit> &retained, int *work, InputSlice ignored) const
{
	if (ignored.cell) {
		log_assert(cells_.count(ignored.cell) && cell_input(ignored.cell->type, ignored.port) && ignored.offset >= 0 && ignored.width >= 0);
		log_assert(ignored.offset <= GetSize(port(ignored.cell, ignored.port)) - ignored.width);
	}
	pool<Cell *> result = region;
	result.insert(roots.begin(), roots.end());
	pool<SigBit> replaced, leaves;
	for (auto bit : targets)
		replaced.insert(sigmap_(bit));
	for (auto bit : retained)
		leaves.insert(sigmap_(bit));
	bool changed;
	do {
		changed = false;
		for (auto cell : std::vector<Cell *>(result.begin(), result.end())) {
			log_assert(cell && cells_.count(cell));
			bool preserve = !editable_cell(cell);
			bool has_outputs = false;
			for (const auto &[name, signal] : cell->connections()) {
				if (preserve || !cell_output(cell->type, name))
					continue;
				const auto &output = port(cell, name);
				has_outputs |= !output.empty();
				for (int i = 0; i < GetSize(output); i++) {
					if (work && --*work < 0)
						return {};
					auto bit = output[i];
					if (!editable_output(cell, name, i, bit) || leaves.count(bit)) {
						preserve = true;
						break;
					}
					if (replaced.count(bit) && (roots.empty() || roots.count(cell)))
						continue;
					if (protected_bit(bit)) {
						preserve = true;
						break;
					}
					for (const auto &user : users(bit)) {
						if (work && --*work < 0)
							return {};
						if (result.count(user.cell) || (user.cell == ignored.cell && user.port == ignored.port &&
								user.offset >= ignored.offset && user.offset - ignored.offset < ignored.width))
							continue;
						preserve = true;
						break;
					}
					if (preserve)
						break;
				}
			}
			if (preserve || !has_outputs) {
				result.erase(cell);
				changed = true;
			}
		}
	} while (changed);
	return result;
}

void PmuxNetlist::disconnect_outputs(Cell *cell, const pool<SigBit> &targets)
{
	log_assert(cell && cells_.count(cell));
	pool<SigBit> replaced;
	for (auto bit : targets)
		replaced.insert(sigmap_(bit));
	std::vector<std::pair<IdString, SigSpec>> updates;
	for (const auto &[name, signal] : cell->connections()) {
		if (cell_port_dir(cell->type, name) != RTLIL::PD_OUTPUT)
			continue;
		const auto &output = port(cell, name);
		SigSpec replacement = signal;
		for (int i = 0; i < GetSize(output); i++)
			if (replaced.count(output[i])) {
				log_assert(editable_bit(cell, name, i));
				replacement[i] = SigBit(module_->addWire(NEW_ID));
			}
		if (replacement != signal)
			updates.emplace_back(name, std::move(replacement));
	}
	for (const auto &[name, signal] : updates)
		set_port(cell, name, signal);
}

YOSYS_NAMESPACE_END
