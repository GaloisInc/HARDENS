module Coincidence_2_4
    ( input logic [3:0] x,
      output logic out
    );
    // ../models/RTS/Actuation.cry:53:1--53:16
    assign out = (x != 4'h0) & ((x != 4'h1) & ((x != 4'h2) & ((x != 4'h4) & (x != 4'h8))));
endmodule
module Vote
    #(localparam lg2 = 2)
    ( input logic [lg2 - 1:0] ch,
      input logic [95:0] inp,
      output logic out
    );
    // ../models/RTS/Actuation.cry:50:1--50:5
    logic [3:0] temp1;
    genvar gv0;
    for (gv0 = 0; gv0 < 4; gv0 = gv0 + 1)
      begin: for_blk
        logic [23:0] i;
        assign i[23:0] = inp[24 * (3 - gv0 % 4) + 23-:24];
        assign temp1[3 - gv0] = i[8 * (2 - ch) + 7-:8] == 8'h1;
      end: for_blk
    Coincidence_2_4 Coincidence_2_4_inst1 (.x(temp1),
                                           .out(out));
endmodule
module Voting_Step
    ( input logic [95:0] inp,
      input logic [1:0] old_votes,
      output logic [1:0] out
    );
    logic d0;
    logic d1;
    // ../models/RTS/Actuation.cry:46:5--46:7
    logic Vote_out;
    Vote Vote_inst1 (.ch(2'h0),
                     .inp(inp),
                     .out(Vote_out));
    logic Vote_out1;
    Vote Vote_inst2 (.ch(2'h1),
                     .inp(inp),
                     .out(Vote_out1));
    assign d0 = Vote_out | (Vote_out1 | old_votes[1]);
    // ../models/RTS/Actuation.cry:47:5--47:7
    logic Vote_out2;
    Vote Vote_inst3 (.ch(2'h2),
                     .inp(inp),
                     .out(Vote_out2));
    assign d1 = Vote_out2 | old_votes[0];
    // ../models/RTS/Actuation.cry:42:1--42:12
    assign out[1] = d0;
    assign out[0] = d1;
endmodule
