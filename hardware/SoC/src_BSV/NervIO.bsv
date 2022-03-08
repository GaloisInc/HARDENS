package NervIO;

// Encapsulate IO access
interface NervIO_IFC;
    // Return True if the address is within the memory
    // mapped IO region
    method Bool is_io_mem_addr(Bit #(32) m_dmem_addr);
    // Perform IO operation
    method Bit #(32) io_mem_op(Bit #(32) m_dmem_addr,
                               Bit #(32) wdata,
                               Bit #(32) mask);
endinterface

(* synthesize *)
module mkNervIO(NervIO_IFC);
    Bit #(32) io_base_addr = 32'h 0100_0000;

    // IO addresses
    Bit #(32) gpio_addr = 32'h 0100_0000;

    // TODO: use offsets
    Bit #(32) uart_reg_addr_tx = 32'h 0200_0000;
    Bit #(32) uart_reg_addr_rx = 32'h 0200_0004;
    Bit #(32) uart_reg_addr_dr = 32'h 0200_0008;
    Bit #(32) i2c_reg_addr_base = 32'h 0300_0000;
    Bit #(32) i2c_reg_addr_data = 32'h 0300_0004; // I2C fifo has up to 16 bytes (4 registers)
    Bit #(32) i2c_reg_addr_stat = 32'h 0300_0008; // I2C status reg (transaction complete 1bit, transaction error 1bit, error type 2bits)
    Bit #(32) clock_reg_adrr_lower = 32'h 0400_0000; // System ticks
    Bit #(32) clock_reg_adrr_upper = 32'h 0400_0004;

    Bit #(32) instr_reg_addr_hand_base           = 32'h 0500_0000;// Handwritten Instrumentation base register
    Bit #(32) instr_reg_addr_hand_instr_val_0    = 32'h 0500_0004;
    Bit #(32) instr_reg_addr_hand_instr_val_1    = 32'h 0500_0008;
    Bit #(32) instr_reg_addr_hand_instr_val_2    = 32'h 0500_000C;
    Bit #(32) instr_reg_addr_hand_setpoint_val_0 = 32'h 0500_0010;
    Bit #(32) instr_reg_addr_hand_setpoint_val_1 = 32'h 0500_0014;
    Bit #(32) instr_reg_addr_hand_setpoint_val_2 = 32'h 0500_0018;
    Bit #(32) instr_reg_addr_hand_res            = 32'h 0500_001C;

    Bit #(32) instr_reg_addr_gen_base           = 32'h 0500_0020;// Generated Instrumentation base register
    Bit #(32) instr_reg_addr_gen_instr_val_0    = 32'h 0500_0024;
    Bit #(32) instr_reg_addr_gen_instr_val_1    = 32'h 0500_0028;
    Bit #(32) instr_reg_addr_gen_instr_val_2    = 32'h 0500_002C;
    Bit #(32) instr_reg_addr_gen_setpoint_val_0 = 32'h 0500_0030;
    Bit #(32) instr_reg_addr_gen_setpoint_val_1 = 32'h 0500_0034;
    Bit #(32) instr_reg_addr_gen_setpoint_val_2 = 32'h 0500_0038;
    Bit #(32) instr_reg_addr_gen_res            = 32'h 0500_003C;

    Bit #(32) actuation_reg_addr_gen_base       = 32'h 0500_0040;// Generated Actuation base register
    Bit #(32) actuation_reg_addr_gen_trip_0     = 32'h 0500_0044;
    Bit #(32) actuation_reg_addr_gen_trip_1     = 32'h 0500_0048;
    Bit #(32) actuation_reg_addr_gen_trip_2     = 32'h 0500_004C;
    Bit #(32) actuation_reg_addr_gen_res        = 32'h 0500_0050;

    Bit #(32) io_top_addr  = 32'h 0500_0050;

    method Bool is_io_mem_addr(Bit #(32) m_dmem_addr);
        begin
            if ((m_dmem_addr >= io_base_addr) && (m_dmem_addr <= io_top_addr))
                return True;
            else
                return False;
        end
    endmethod

    method Bit #(32) io_mem_op(Bit #(32) m_dmem_addr,
                               Bit #(32) wdata,
                               Bit #(32) mask);
        begin
            // Clock submodule
            // Instrumentation submodule
            // Actuation submodule
            return 0;
        end
    endmethod
endmodule

endpackage