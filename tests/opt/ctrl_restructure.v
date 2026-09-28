module ctrl_restructure_mux(
	input clk, en, sel, input [7:0] a, b, output reg [7:0] q
);
	always @(posedge clk)
		q <= (a & {8{en & ~sel}}) | (b & {8{en & sel}}) | (q & {8{~en}});
endmodule

module ctrl_restructure_reconvergent(
	input clk, sel, input [7:0] a, b, output reg [7:0] q
);
	wire [7:0] chosen = sel ? a : q;
	always @(posedge clk)
		q <= (chosen | b) & (chosen | ~b);
endmodule

module ctrl_restructure_reject_overlap(
	input clk, s0, s1, input [7:0] a, b, output reg [7:0] q
);
	always @(posedge clk)
		q <= (a & {8{s0}}) | (b & {8{s1}});
endmodule

module ctrl_restructure_reject_partial(
	input clk, s0, s1, input [7:0] a, b, output reg [7:0] q
);
	always @(posedge clk)
		q <= (a & {{4{s0}}, {4{s1}}}) | (b & {{4{~s0}}, {4{~s1}}});
endmodule

module ctrl_restructure_pmux(
	input clk, input [1:0] sel, input [7:0] a, b, output reg [7:0] q
);
	always @(posedge clk)
		case (sel)
			2'b01: q <= a;
			2'b10: q <= b;
			default: q <= q;
		endcase
endmodule

module ctrl_restructure_with_unknown(
	input clk, en, input [7:0] a, output reg [7:0] q, xq
);
	always @(posedge clk) begin
		q <= en ? a : q;
		xq <= en ? 8'hxx : xq;
	end
endmodule

module ctrl_restructure_existing_ce(
	input clk, en, reset, update, input [7:0] a, output reg [7:0] q
);
	always @(posedge clk)
		if (en)
			if (reset)
				q <= 8'h5a;
			else if (update)
				q <= a;
endmodule

module ctrl_restructure_shared_control(
	input clk, en, valid, input [63:0] a,
	output reg [63:0] q0, q1, q2
);
	wire update = ~(en & valid);
	always @(posedge clk) begin
		q0 <= update ? a : q0;
		q1 <= update ? q0 : q1;
		q2 <= update ? q1 : q2;
	end
endmodule

module ctrl_restructure_reject_uncovered(
	input clk, en, sel, input [7:0] a, b, output reg [7:0] q
);
	always @(posedge clk)
		q <= (a & {8{en & ~sel}}) | (b & {8{en & sel}});
endmodule

module ctrl_restructure_with_cycle(
	input clk, en, input [7:0] a, output reg [7:0] q, cq
);
	wire cycle;
	assign cycle = en & cycle;
	always @(posedge clk) begin
		q <= en ? a : q;
		cq <= cycle ? a : cq;
	end
endmodule
