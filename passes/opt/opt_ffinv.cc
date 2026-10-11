/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2022  Marcelina Kościelnicka <mwk@0x04.net>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/modtools.h"
#include "kernel/ffinit.h"
#include "kernel/ff.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct OptFfInvWorker
{
	int count = 0;
	RTLIL::Module *module;
	ModIndex index;
	FfInitVals initvals;

	// 反相 $lut：一位宽且真值表为 NOT。
	static bool inverting_lut(Cell *cell)
	{
		return cell->type.in(ID($lut)) && cell->getParam(ID::WIDTH) == 1 &&
				cell->getParam(ID::LUT).as_int() == 1;
	}

	// Case 1:
	// - FF is driven by inverter
	// - ... which has no other users
	// - all users of FF are LUTs
	bool push_d_inv(FfData &ff) {
		log_assert(ff.width == 1);
		if (index.query_is_input(ff.sig_d))
			return false;
		if (index.query_is_output(ff.sig_d))
			return false;
		auto d_ports = index.query_ports(ff.sig_d);
		if (d_ports.size() != 2)
			return false;
		Cell *d_inv = nullptr;
		for (auto &port: d_ports) {
			if (port.cell == ff.cell && port.port == ID::D)
				continue;
			if (port.port != ID::Y)
				return false;
			if (!port.cell->type.in(ID($not), ID($_NOT_)) && !inverting_lut(port.cell))
				return false;
			// d_ports 恰有两个端口，其中一个是本 FF 的 D，因此这里至多执行一次
			d_inv = port.cell;
		}

		if (index.query_is_output(ff.sig_q))
			return false;
		auto q_ports = index.query_ports(ff.sig_q);
		pool<Cell *> q_luts;
		for (auto &port: q_ports) {
			if (port.cell == ff.cell && port.port == ID::Q)
				continue;
			if (port.cell == d_inv)
				return false;
			if (port.port != ID::A)
				return false;
			if (!port.cell->type.in(ID($not), ID($_NOT_), ID($lut)))
				return false;
			q_luts.insert(port.cell);
		}

		ff.flip_rst_bits({0});
		ff.sig_d = d_inv->getPort(ID::A);

		for (Cell *lut: q_luts) {
			if (lut->type == ID($lut)) {
				int flip_mask = 0;
				SigSpec sig_a = lut->getPort(ID::A);
				for (int i = 0; i < GetSize(sig_a); i++) {
					if (index.sigmap(sig_a[i]) == index.sigmap(ff.sig_q[0])) {
						flip_mask |= 1 << i;
					}
				}
				Const mask = lut->getParam(ID::LUT);
				Const::Builder new_mask_builder(1 << GetSize(sig_a));
				for (int j = 0; j < (1 << GetSize(sig_a)); j++)
					new_mask_builder.push_back(mask[j ^ flip_mask]);
				Const new_mask = new_mask_builder.build();
				if (GetSize(sig_a) == 1 && new_mask.as_int() == 2) {
					module->connect(lut->getPort(ID::Y), ff.sig_q);
					module->remove(lut);
				} else {
					lut->setParam(ID::LUT, new_mask);
				}
			} else {
				// it was an inverter
				module->connect(lut->getPort(ID::Y), ff.sig_q);
				module->remove(lut);
			}
		}

		ff.emit();
		return true;
	}

	// Case 2:
	// - FF is driven by LUT
	// - ... which has no other users
	// - FF has one user
	// - ... which is an inverter
	bool push_q_inv(FfData &ff) {
		if (index.query_is_input(ff.sig_d))
			return false;
		if (index.query_is_output(ff.sig_d))
			return false;

		Cell *d_lut = nullptr;
		auto d_ports = index.query_ports(ff.sig_d);
		if (d_ports.size() != 2)
			return false;
		for (auto &port: d_ports) {
			if (port.cell == ff.cell && port.port == ID::D)
				continue;
			if (port.port != ID::Y)
				return false;
			if (!port.cell->type.in(ID($not), ID($_NOT_), ID($lut)))
				return false;
			// d_ports 恰有两个端口，其中一个是本 FF 的 D，因此这里至多执行一次
			d_lut = port.cell;
		}

		if (index.query_is_output(ff.sig_q))
			return false;
		auto q_ports = index.query_ports(ff.sig_q);
		if (q_ports.size() != 2)
			return false;
		Cell *q_inv = nullptr;
		for (auto &port: q_ports) {
			if (port.cell == ff.cell && port.port == ID::Q)
				continue;
			if (port.cell == d_lut)
				return false;
			if (port.port != ID::A)
				return false;
			if (!port.cell->type.in(ID($not), ID($_NOT_)) && !inverting_lut(port.cell))
				return false;
			// q_ports 恰有两个端口，其中一个是本 FF 的 Q，因此这里至多执行一次
			q_inv = port.cell;
		}

		ff.flip_rst_bits({0});
		ff.sig_q = q_inv->getPort(ID::Y);
		module->remove(q_inv);

		if (d_lut->type == ID($lut)) {
			Const mask = d_lut->getParam(ID::LUT);
			Const::Builder new_mask_builder(GetSize(mask));
			for (int i = 0; i < GetSize(mask); i++) {
				if (mask[i] == State::S0)
					new_mask_builder.push_back(State::S1);
				else
					new_mask_builder.push_back(State::S0);
			}
			Const new_mask = new_mask_builder.build();
			d_lut->setParam(ID::LUT, new_mask);
			if (d_lut->getParam(ID::WIDTH) == 1 && new_mask.as_int() == 2) {
				module->connect(ff.sig_d, d_lut->getPort(ID::A));
				module->remove(d_lut);
			}
		} else {
			// it was an inverter
			module->connect(ff.sig_d, d_lut->getPort(ID::A));
			module->remove(d_lut);
		}

		ff.emit();
		return true;
	}

	OptFfInvWorker(RTLIL::Module *module) :
		module(module), index(module), initvals(&index.sigmap, module)
	{
		log("Discovering LUTs.\n");

		std::vector<Cell *> ffs;

		for (Cell *cell : module->selected_cells())
			if (cell->is_builtin_ff())
				ffs.push_back(cell);

		for (Cell *cell : ffs) {
			FfData ff(&initvals, cell);
			if (ff.has_sr)
				continue;
			if (!ff.has_clk)
				continue;
			if (ff.has_aload)
				continue;
			if (ff.width != 1)
				continue;

			if (push_d_inv(ff)) {
				count++;
			} else if (push_q_inv(ff)) {
				count++;
			}
		}
	}
};

struct OptFfInvPass : public Pass {
	OptFfInvPass() : Pass("opt_ffinv", "push inverters through FFs") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_ffinv [selection]\n");
		log("\n");
		log("This pass pushes inverters to the other side of a FF when they can be merged\n");
		log("into LUTs on the other side.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_FFINV pass (push inverters through FFs).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			break;
		}
		extra_args(args, argidx, design);

		int total_count = 0;
		for (auto module : design->selected_modules())
		{
			OptFfInvWorker worker(module);
			total_count += worker.count;
		}
		if (total_count)
			design->scratchpad_set_bool("opt.did_something", true);
		log("Pushed %d inverters.\n", total_count);
	}
} OptFfInvPass;

static bool ffphase_protected_cell(Cell *cell)
{
	return cell->has_keep_attr() || cell->get_bool_attribute(ID::lut_keep);
}

static pool<SigBit> ffphase_protected_bits(Module *module, SigMap &sigmap)
{
	pool<SigBit> result;
	for (auto wire : module->wires()) {
		if (!wire->get_bool_attribute(ID::keep) && !wire->get_bool_attribute(ID::lut_keep))
			continue;
		for (int i = 0; i < wire->width; i++)
			result.insert(sigmap(SigBit(wire, i)));
	}
	return result;
}

// OptFfPhase：自由初态 FF 的状态极性转换。
// -prepare 在 generic dfflegalize 之后、ff_map 之前运行，只依据 SigMap、FfInitVals 与保护位
// 把初态未指定且异步复位不活动的 $_DFFE_PN0P_ 记入内部 bool 属性 $ffphase_free_init。
// 默认模式在 cells_map 之后的 native 网表上运行：把这类 FF 的 Q 换成某个原 Q-NOT 的输出，
// 并按位翻转消费原 Q 的普通 LC 真值表与输入，使自由初态可以选择 q0=1 而物理初态仍为 low。
struct OptFfPhasePrepareWorker
{
	int count = 0;
	SigMap sigmap;
	FfInitVals initvals;
	pool<SigBit> protected_bits;

	// 资格：真实 generic FF、异步复位不活动、Q 初态未指定且没有保护。
	bool is_free_init_ff(Cell *cell)
	{
		if (ffphase_protected_cell(cell))
			return false;
		SigBit r = sigmap(cell->getPort(ID::R).as_bit());
		if (r.wire != nullptr || r.data != State::S1)
			return false;
		SigBit q = sigmap(cell->getPort(ID::Q).as_bit());
		if (q.wire == nullptr || protected_bits.count(q))
			return false;
		return initvals(q) == State::Sx;
	}

	OptFfPhasePrepareWorker(RTLIL::Module *module) :
		sigmap(module), initvals(&sigmap, module),
		protected_bits(ffphase_protected_bits(module, sigmap))
	{
		// 重复 prepare 清除旧资格，属性始终反映当前 selection 的图形。
		for (Cell *cell : module->selected_cells()) {
			if (cell->type == ID($_DFFE_PN0P_) && is_free_init_ff(cell)) {
				cell->set_bool_attribute(ID($ffphase_free_init));
				count++;
			} else {
				cell->attributes.erase(ID($ffphase_free_init));
			}
		}
	}
};

// native 转换：old_q 换成某个原 Q-NOT 的输出，消费原 Q 的普通 LC 按统一公式改写。
struct OptFfPhaseWorker
{
	int count = 0;
	RTLIL::Module *module;
	ModIndex index;
	FfInitVals initvals;
	pool<SigBit> protected_bits;

	// 集中提交时只保留 FF 端口与需要删除的 NOT。
	struct Plan
	{
		Cell *ff = nullptr;
		SigBit new_q;
		Cell *chosen_not = nullptr;
		std::vector<Cell *> drop_nots;
	};

	struct LutPhase
	{
		int inputs = 0;
		bool output = false;
	};
	dict<Cell *, LutPhase> lc_phase;
	dict<SigBit, SigBit> replaced_q;
	std::vector<Plan> plans;

	// 实际输入端口：方向已知、为输入且不是输出；未知或双向端口返回 false。
	static bool is_input(Cell *cell, IdString port)
	{
		return cell->input(port) && !cell->output(port);
	}

	// 实际输出端口：方向已知、为输出且不是输入。
	static bool is_output(Cell *cell, IdString port)
	{
		return cell->output(port) && !cell->input(port);
	}

	// $not 可能是向量，只接受 A 与 Y 各一位的实例。
	bool is_one_bit_not(Cell *cell)
	{
		return cell->type.in(ID($not), ID($_NOT_)) &&
				GetSize(cell->getPort(ID(A))) == 1 && GetSize(cell->getPort(ID(Y))) == 1;
	}

	// dataa 是最低索引位，与 LC 的 lut_mask 地址位一致；data_port() 与 input_index() 是同一映射的两向查表。
	static const IdString &data_port(int index)
	{
		static const IdString ports[4] = {ID(dataa), ID(datab), ID(datac), ID(datad)};
		log_assert(index >= 0 && index < 4);
		return ports[index];
	}

	static int input_index(IdString port)
	{
		for (int i = 0; i < 4; i++) if (data_port(i) == port) return i;
		log_assert(false);
		return -1;
	}

	// cout 可以完全省略，也可以接没有消费者的悬空网络；其它端口都是实际观察或额外驱动。
	bool cout_unobserved(Cell *lc)
	{
		if (!lc->hasPort(ID(cout)))
			return true;
		SigBit bit = index.sigmap(lc->getPort(ID(cout)).as_bit());
		if (bit.wire == nullptr)
			return true;
		if (index.query_is_input(bit) || index.query_is_output(bit) ||
				protected_bits.count(bit) || initvals(bit) != State::Sx)
			return false;
		for (auto &port : index.query_ports(bit))
			if (port.cell != lc || port.port != ID(cout))
				return false;
		return true;
	}

	// combout 无保护、无已知初值、不是模块输入，其它端口都是真实输入，实际驱动只有该 LC。
	bool combout_free(Cell *lc)
	{
		SigBit out = index.sigmap(lc->getPort(ID(combout)).as_bit());
		if (out.wire == nullptr || protected_bits.count(out) || initvals(out) != State::Sx)
			return false;
		if (index.query_is_input(out))
			return false;
		for (auto &port : index.query_ports(out))
			if ((port.cell != lc || port.port != ID(combout)) && !is_input(port.cell, port.port))
				return false;
		return true;
	}

	// 普通 LC：真值表只由 dataa..datad 决定，carry 角色与 cin/cout 连接保持不动。
	bool is_plain_lc(Cell *lc)
	{
		if (lc->type != ID(cycloneiv_lcell_comb) || !module->selected(lc) || ffphase_protected_cell(lc))
			return false;
		if (!lc->hasParam(ID(sum_lutc_input)) || !lc->hasParam(ID(lut_mask)))
			return false;
		if (lc->getParam(ID(sum_lutc_input)).decode_string() != "datac")
			return false;
		Const mask = lc->getParam(ID(lut_mask));
		if (GetSize(mask) != 16 || !mask.is_fully_def())
			return false;
		for (auto &attr : lc->attributes)
			if (attr.first.in(ID(cycloneiv_carry_chain), ID(cycloneiv_carry_index), ID(cycloneiv_carry_mask),
					ID(cycloneiv_carry_role), ID(cycloneiv_carry_bi), ID(cycloneiv_carry_x)))
				return false;
		return cout_unobserved(lc) && combout_free(lc);
	}

	bool is_const_bit(SigBit raw, State value)
	{
		SigBit bit = index.sigmap(raw);
		return bit.wire == nullptr && bit.data == value;
	}

	bool collect_plan(Cell *ff, Plan &plan)
	{
		// 只处理带 prepare 资格属性、保持 FF_MAP 配置的 native FF。
		if (ff->type != ID(dffeas) || !ff->get_bool_attribute(ID($ffphase_free_init)))
			return false;
		if (ffphase_protected_cell(ff))
			return false;
		if (ff->getParam(ID(is_wysiwyg)).decode_string() != "TRUE" ||
				ff->getParam(ID(power_up)).decode_string() != "low")
			return false;
		if (!is_const_bit(ff->getPort(ID(clrn)).as_bit(), State::S1) ||
				!is_const_bit(ff->getPort(ID(prn)).as_bit(), State::S1))
			return false;
		for (auto port : {ID(aload), ID(asdata), ID(sclr), ID(sload)})
			if (!is_const_bit(ff->getPort(port).as_bit(), State::S0))
				return false;

		SigBit old_q = index.sigmap(ff->getPort(ID(q)).as_bit());
		if (old_q.wire == nullptr || protected_bits.count(old_q) || initvals(old_q) != State::Sx)
			return false;
		if (index.query_is_input(old_q) || index.query_is_output(old_q))
			return false;

		// 原 Q 只允许被普通 LC 的 dataa..datad 与一位 NOT 的 A 消费。
		std::vector<Cell *> nots;
		dict<Cell *, int> input_phase;
		for (auto &port : index.query_ports(old_q)) {
			if (port.cell == ff && port.port == ID(q))
				continue;
			if (!is_input(port.cell, port.port))
				return false;
			if (is_one_bit_not(port.cell) && port.port == ID(A)) {
				nots.push_back(port.cell);
				continue;
			}
			if (port.cell->type != ID(cycloneiv_lcell_comb) ||
					!port.port.in(ID(dataa), ID(datab), ID(datac), ID(datad)))
				return false;
			if (!is_plain_lc(port.cell))
				return false;
			input_phase[port.cell] |= 1 << input_index(port.port);
		}
		if (nots.empty())
			return false;

		// 全部消费原 Q 的 NOT 都会被删除：必须随选择、无保护，Y 由它唯一驱动且没有已知初值。
		Cell *chosen = nullptr;
		for (Cell *not_cell : nots) {
			if (!module->selected(not_cell) || ffphase_protected_cell(not_cell))
				return false;
			SigBit y = index.sigmap(not_cell->getPort(ID(Y)).as_bit());
			if (y.wire == nullptr || index.query_is_input(y) || protected_bits.count(y) || initvals(y) != State::Sx)
				return false;
			for (auto &port : index.query_ports(y))
				if ((port.cell != not_cell || port.port != ID(Y)) && !is_input(port.cell, port.port))
					return false;
			if (chosen == nullptr || not_cell->name.str() < chosen->name.str())
				chosen = not_cell;
		}

		// FF.d 的端口集合只有该 FF 与一个普通 LC 的 combout，没有模块端口和已知初值。
		SigBit d = index.sigmap(ff->getPort(ID(d)).as_bit());
		if (d.wire == nullptr || protected_bits.count(d) || initvals(d) != State::Sx)
			return false;
		if (index.query_is_input(d) || index.query_is_output(d))
			return false;
		auto d_ports = index.query_ports(d);
		if (d_ports.size() != 2)
			return false;
		Cell *d_lc = nullptr;
		for (auto &port : d_ports) {
			if (port.cell == ff && port.port == ID(d))
				continue;
			if (port.port != ID(combout) || !is_output(port.cell, port.port))
				return false;
			d_lc = port.cell;
		}
		if (d_lc == nullptr || !is_plain_lc(d_lc))
			return false;

		plan.ff = ff;
		plan.new_q = chosen->getPort(ID(Y)).as_bit();
		plan.chosen_not = chosen;
		for (Cell *not_cell : nots)
			if (not_cell != chosen)
				plan.drop_nots.push_back(not_cell);
		replaced_q[old_q] = plan.new_q;
		for (auto &entry : input_phase)
			lc_phase[entry.first].inputs |= entry.second;
		lc_phase[d_lc].output ^= true;
		return true;
	}

	// 集中提交：先按原图重写 LC 真值表与输入，再改 FF 端口并删除原 NOT。
	void commit()
	{
		for (auto &entry : lc_phase) {
			Cell *lc = entry.first;
			int input_phase = entry.second.inputs;
			uint16_t mask = lc->getParam(ID(lut_mask)).as_int();
			if (input_phase != 0) {
				uint16_t permuted = 0;
				for (int row = 0; row < 16; row++)
					if (mask & (uint16_t(1) << (row ^ input_phase)))
						permuted |= uint16_t(1) << row;
				mask = permuted;
				for (int bit_index = 0; bit_index < 4; bit_index++) {
					if (!(input_phase & (1 << bit_index)))
						continue;
					IdString port = data_port(bit_index);
					lc->setPort(port, replaced_q.at(index.sigmap(lc->getPort(port).as_bit())));
				}
			}
			if (entry.second.output)
				mask ^= 0xffff;
			lc->setParam(ID(lut_mask), Const(mask, 16));
		}
		for (auto &plan : plans) {
			plan.ff->setPort(ID(q), plan.new_q);
			module->remove(plan.chosen_not);
			for (Cell *not_cell : plan.drop_nots) {
				module->connect(not_cell->getPort(ID(Y)), plan.new_q);
				module->remove(not_cell);
			}
		}
	}

	OptFfPhaseWorker(RTLIL::Module *module) :
		module(module), index(module), initvals(&index.sigmap, module),
		protected_bits(ffphase_protected_bits(module, index.sigmap))
	{
		// 先在原图上收集全部合格计划，再集中提交，避免中途重建索引。
		for (Cell *cell : module->selected_cells()) {
			Plan plan;
			if (collect_plan(cell, plan)) {
				plans.push_back(std::move(plan));
				count++;
			}
			// 选中单元的资格属性就地清除，包含未被接受的候选 FF。
			cell->attributes.erase(ID($ffphase_free_init));
		}
		commit();
	}
};

struct OptFfPhasePass : public Pass {
	OptFfPhasePass() : Pass("opt_ffphase", "flip the state polarity of free-init FFs") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_ffphase [-prepare] [selection]\n");
		log("\n");
		log("Without options this pass moves the output of free-init native FFs to an existing\n");
		log("inverter, so that the inverter can be removed. The data inputs and the LUT mask of\n");
		log("every ordinary Cyclone IV LUT that consumes the old state are rearranged for the\n");
		log("new state polarity, and the mask of the private LUT driving the FF data input is\n");
		log("complemented as well.\n");
		log("\n");
		log("    -prepare\n");
		log("        record which generic FFs have a free initial state and an inactive async\n");
		log("        reset before FF mapping.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_FFPHASE pass (flip free-init FF state polarity).\n");

		bool prepare = false;
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-prepare") {
				prepare = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		int total_count = 0;
		for (auto module : design->selected_modules())
		{
			if (prepare) {
				OptFfPhasePrepareWorker worker(module);
				total_count += worker.count;
			} else {
				OptFfPhaseWorker worker(module);
				total_count += worker.count;
			}
		}
		if (prepare) {
			log("Marked %d free-init FFs.\n", total_count);
			return;
		}
		log("Flipped %d FFs.\n", total_count);
	}
} OptFfPhasePass;

PRIVATE_NAMESPACE_END
