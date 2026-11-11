#ifndef PMUX_NETLIST_H
#define PMUX_NETLIST_H

#include "kernel/newcelltypes.h"
#include "kernel/sigtools.h"

#include <memory>

YOSYS_NAMESPACE_BEGIN

class PmuxNetlist {
public:
	struct PortBit {
		RTLIL::Cell *cell;
		RTLIL::IdString port;
		int offset;
	};
	using Driver = PortBit;
	using User = PortBit;

	struct InputSlice {
		RTLIL::Cell *cell;
		RTLIL::IdString port;
		int offset, width;
		InputSlice(RTLIL::Cell *cell = nullptr, RTLIL::IdString port = {}, int offset = 0, int width = 0)
			: cell(cell), port(port), offset(offset), width(width) {}
	};

	class Dependencies {
	public:
		Dependencies(const PmuxNetlist &netlist, const pool<RTLIL::SigBit> &targets, int &work,
			bool track_high_z = false, pool<RTLIL::SigBit> *references = nullptr);
		bool visit(RTLIL::SigBit bit);
		bool high_z(RTLIL::SigBit bit) const;

	private:
		enum class State { Active, Logic, HighZ, Unresolved };
		const PmuxNetlist &netlist_;
		pool<RTLIL::SigBit> targets_;
		int &work_;
		bool track_high_z_;
		pool<RTLIL::SigBit> *references_;
		std::size_t revision_;
		dict<RTLIL::SigBit, State> state_;

		bool visit(RTLIL::SigBit bit, int depth);
		bool output_high_z(const Driver &source, const RTLIL::SigSpec &inputs) const;
	};

	PmuxNetlist(RTLIL::Module *module, RTLIL::Design *design);
	RTLIL::Module *module() const { return module_; }
	const SigMap &sigmap() const { return sigmap_; }
	std::size_t revision() const { return revision_; }

	bool cell_evaluable(RTLIL::IdString type) const;
	RTLIL::PortDir cell_port_dir(RTLIL::IdString type, RTLIL::IdString port) const;
	bool cell_input(RTLIL::IdString type, RTLIL::IdString port) const;
	bool cell_output(RTLIL::IdString type, RTLIL::IdString port) const;

	// 端口引用可跨其他端口的查询与单元登记使用，直到该端口被编辑、注销或信号连接发生变化。
	const RTLIL::SigSpec &port(RTLIL::Cell *cell, RTLIL::IdString name) const;
	RTLIL::SigBit operand(RTLIL::Cell *cell, RTLIL::IdString name, int offset) const;
	RTLIL::SigSpec extended(RTLIL::Cell *cell, RTLIL::IdString name, int width) const;

	// 模块输入的唯一驱动记录没有单元，无法确定唯一驱动时返回空指针。
	const Driver *source(RTLIL::SigBit bit) const;
	RTLIL::Cell *driver(RTLIL::SigBit bit) const;
	bool unique(RTLIL::SigBit bit) const { return source(bit) != nullptr; }
	bool kept(RTLIL::SigBit bit) const;
	bool protected_bit(RTLIL::SigBit bit) const;
	bool uncertain(RTLIL::SigBit bit) const;
	bool uncertain_cell(RTLIL::Cell *cell) const;
	bool selected(RTLIL::Cell *cell) const;
	bool editable(RTLIL::Cell *cell, RTLIL::IdString name = ID::Y) const;
	bool editable_bit(RTLIL::Cell *cell, RTLIL::IdString name, int offset) const;
	const pool<RTLIL::SigBit> &protected_bits() const { return protected_bits_; }
	const std::vector<User> &users(RTLIL::SigBit bit) const;

	bool combinational_inputs(RTLIL::SigBit bit, RTLIL::SigSpec &inputs) const;
	bool independent(const pool<RTLIL::SigBit> &leaves, const pool<RTLIL::SigBit> &targets, int &work) const;
	bool private_signal(const RTLIL::SigSpec &signal, const pool<RTLIL::Cell *> &allowed) const;
	pool<RTLIL::Cell *> private_cells(const pool<RTLIL::Cell *> &region, const pool<RTLIL::Cell *> &roots,
		const pool<RTLIL::SigBit> &targets, const pool<RTLIL::SigBit> &retained,
		int *work = nullptr, InputSlice ignored = InputSlice()) const;

	void register_cell(RTLIL::Cell *cell);
	void forget_cell(RTLIL::Cell *cell);
	void set_port(RTLIL::Cell *cell, RTLIL::IdString name, const RTLIL::SigSpec &signal);
	void connect(const RTLIL::SigSpec &lhs, const RTLIL::SigSpec &rhs);
	void disconnect_outputs(RTLIL::Cell *cell, const pool<RTLIL::SigBit> &targets);

private:
	struct BitInfo {
		int inputs = 0, outputs = 0, keeps = 0, uncertain_ports = 0;
		std::vector<Driver> drivers;
		bool uncertain() const { return uncertain_ports != 0 || inputs + GetSize(drivers) > 1; }
		bool protected_bit() const { return outputs != 0 || keeps != 0 || uncertain_ports != 0; }
		bool empty() const { return inputs == 0 && !protected_bit() && drivers.empty(); }
	};
	struct CellInfo {
		bool selected;
		bool keep;
		int uncertain_ports = 0;
	};
	struct CachedPort {
		RTLIL::SigSpec signal;
		std::size_t alias_revision;
	};

	RTLIL::Module *module_;
	RTLIL::Design *design_;
	SigMap sigmap_;
	NewCellTypes types_;
	dict<RTLIL::SigBit, BitInfo> bits_;
	dict<RTLIL::Cell *, CellInfo> cells_;
	pool<RTLIL::IdString> registered_types_;
	pool<RTLIL::SigBit> protected_bits_;
	mutable dict<RTLIL::SigBit, std::vector<User>> users_;
	mutable bool users_ready_ = false;
	mutable dict<std::pair<RTLIL::Cell *, RTLIL::IdString>, std::unique_ptr<CachedPort>> ports_;
	std::size_t revision_ = 0, alias_revision_ = 0;

	const BitInfo *bit_info(RTLIL::SigBit bit) const;
	bool operand_signed(RTLIL::Cell *cell, RTLIL::IdString name) const;
	bool editable_cell(RTLIL::Cell *cell) const;
	bool editable_output(RTLIL::Cell *cell, RTLIL::IdString name, int offset, RTLIL::SigBit bit) const;
	void index_port(RTLIL::Cell *cell, RTLIL::IdString name, const RTLIL::SigSpec &signal, int delta);
	void index_users(RTLIL::Cell *cell, RTLIL::IdString name, const RTLIL::SigSpec &signal, int delta) const;
	void ensure_users() const;
	void update_protection(RTLIL::SigBit bit, const BitInfo &info);
	void merge_bits(RTLIL::SigBit from, RTLIL::SigBit to);
};

YOSYS_NAMESPACE_END

#endif
