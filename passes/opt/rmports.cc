/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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
// rmports 移除模块及实例的未使用端口；集中删除端口列表中的目标条目，减少重复扫描与移动。
#include "kernel/sigtools.h"
#include "kernel/yosys.h"
#include "kernel/log_help.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct RmportsPassPass : public Pass {
	RmportsPassPass() : Pass("rmports", "remove module ports with no connections") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    rmports [selection]\n");
		log("\n");
		log("This pass identifies ports in the selected modules which are not used or\n");
		log("driven and removes them.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{

		size_t argidx = 1;
		extra_args(args, argidx, design);

		// The set of ports we removed
		dict<IdString, pool<IdString>> removed_ports;

		// Find all of the unused ports, and remove them from that module
		auto modules = design->selected_modules();
		for(auto mod : modules)
			ScanModule(mod, removed_ports);

		// Remove the unused ports from all instances of those modules
		for(auto mod : modules)
			CleanupModule(mod, removed_ports);
	}

	void CleanupModule(Module *module, const dict<IdString, pool<IdString>> &removed_ports)
	{

		auto cells = module->cells();
		for(auto cell : cells)
		{
			auto found = removed_ports.find(cell->type);
			if (found == removed_ports.end())
				continue;

			for (auto port : found->second)
			{
				cell->unsetPort(port);
			}
		}
	}

	void ScanModule(Module* module, dict<IdString, pool<IdString>> &removed_ports)
	{

		pool<IdString> used_ports;

		// See what wires are used.
		// Start by checking connections between named wires
		auto &conns = module->connections();
		for (const auto &sigsig : conns)
		{
			const auto &s1 = sigsig.first;
			const auto &s2 = sigsig.second;
			int len = std::min(GetSize(s1), GetSize(s2));

			for(int i=0; i<len; i++)
			{
				auto w1 = s1[i].wire;
				auto w2 = s2[i].wire;
				if( (w1 == NULL) || (w2 == NULL) )
					continue;


				if (w1->port_input || w1->port_output)
					used_ports.insert(w1->name);

				if (w2->port_input || w2->port_output)
					used_ports.insert(w2->name);
			}
		}

		// Then check connections to cells
		auto cells = module->cells();
		for(auto cell : cells)
		{
			auto &cconns = cell->connections();
			for (const auto &conn : cconns)
			{
				for(int i=0; i<conn.second.size(); i++)
				{
					auto sig = conn.second[i].wire;
					if(sig == NULL)
						continue;

					if (sig->port_input || sig->port_output)
						used_ports.insert(sig->name);
				}
			}
		}

		// Now that we know what IS used, get rid of anything that isn't in that list
		pool<IdString> unused_ports;
		for(auto port : module->ports)
		{
			if(used_ports.find(port) != used_ports.end())
				continue;
			unused_ports.insert(port);
		}

		// 删除端口属性并记录实例中需要移除的端口。
		for(auto port : unused_ports)
		{
			removed_ports[module->name].insert(port);

			// Mark the wire as no longer a port
			auto wire = module->wire(port);
			wire->port_input = false;
			wire->port_output = false;
			wire->port_id = 0;
		}
		module->ports.erase(std::remove_if(module->ports.begin(), module->ports.end(),
				[&](IdString port) { return unused_ports.count(port); }), module->ports.end());

		// Re-number all of the wires that DO have ports still on them
		for(size_t i=0; i<module->ports.size(); i++)
		{
			auto port = module->ports[i];
			auto wire = module->wire(port);
			wire->port_id = i+1;
		}
	}

} RmportsPassPass;

PRIVATE_NAMESPACE_END
