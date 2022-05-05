// Copyright (c) 2022 Rishiyur S. Nikhil, Michal Podhradsky
package NervSoC;

// ================================================================
// Module mkNervSoC is a BSV version of nervsoc.sv

// nervsoc.sv is from:    https://github.com/YosysHQ/nerv

// ================================================================
// Import from BSV library
import RegFile :: *;
import Vector :: *;
import I2C :: *;
import BRAM :: *;
import BRAMCore :: *;

// ================================================================
// Local imports
import Nerv :: *;
import Instrumentation::*;
import Instrumentation_Handwritten_BVI::*;
import Instrumentation_Generated_BVI::*;
import Actuation::*;
import Actuation_Generated_BVI::*;
// ================================================================
// A small NERV SoC

interface NervSoC_IFC;
   // This sets the name of the result
   method Bit #(32) gpio;
   // TX -> a byte to be send
   method ActionValue#(Bit #(8)) get_uart_tx_byte;
   // RX -> a byte to be received
   method Action set_uart_rx_byte(Bit #(8) rx);
   // I2C methods
   method ActionValue #(I2CRequest) i2c_get_request;
   method Action i2c_give_response(I2CResponse r);
endinterface

// ================================================================
typedef enum { REQ_I, PUSH_I, REQ_D, PUSH_D, STOP } State deriving(Bits,Eq);
(* synthesize *)
module mkNervSoC (NervSoC_IFC);
   /**
   * ////////////////////////////////////////////////////////////////
   * Instantiate interfaces
   * ////////////////////////////////////////////////////////////////
   */
   Nerv_IFC nerv <- mkNerv;
   Instrumentation_IFC instr_hand <- mkInstrumentationHandwritten();
   Instrumentation_IFC instr_gen <- mkInstrumentationGenerated();
   Actuation_IFC actuation_gen <- mkActuationGenerated();

   // For debugging only
   Bool show_exec_trace = False;
   Bool show_load_store = False;

   /**
   * ////////////////////////////////////////////////////////////////
   * IO memory map
   * ////////////////////////////////////////////////////////////////
   */
   Bit #(32) io_base_addr                       = 32'h 0100_0000;
   Bit #(32) gpio_addr                          = io_base_addr;

   Bit #(32) uart_reg_addr_tx                   = 32'h 0200_0000;
   Bit #(32) uart_reg_addr_rx                   = 32'h 0200_0004;
   Bit #(32) uart_reg_addr_dr                   = 32'h 0200_0008;
   Bit #(32) i2c_reg_addr_base                  = 32'h 0300_0000;
   Bit #(32) i2c_reg_addr_data                  = 32'h 0300_0004; // I2C fifo has up to 16 bytes (4 registers)
   Bit #(32) i2c_reg_addr_stat                  = 32'h 0300_0008; // I2C status reg (transaction complete 1bit, transaction error 1bit, error type 2bits)
   Bit #(32) clock_reg_adrr_lower               = 32'h 0400_0000; // System ticks
   Bit #(32) clock_reg_adrr_upper               = 32'h 0400_0004;

   Bit #(32) instr_reg_addr_hand_base           = 32'h 0500_0000; // Handwritten Instrumentation base register
   Bit #(32) instr_reg_addr_hand_instr_val_0    = 32'h 0500_0004;
   Bit #(32) instr_reg_addr_hand_instr_val_1    = 32'h 0500_0008;
   Bit #(32) instr_reg_addr_hand_instr_val_2    = 32'h 0500_000C;
   Bit #(32) instr_reg_addr_hand_setpoint_val_0 = 32'h 0500_0010;
   Bit #(32) instr_reg_addr_hand_setpoint_val_1 = 32'h 0500_0014;
   Bit #(32) instr_reg_addr_hand_setpoint_val_2 = 32'h 0500_0018;
   Bit #(32) instr_reg_addr_hand_res            = 32'h 0500_001C;

   Bit #(32) instr_reg_addr_gen_base            = 32'h 0500_0020; // Generated Instrumentation base register
   Bit #(32) instr_reg_addr_gen_instr_val_0     = 32'h 0500_0024;
   Bit #(32) instr_reg_addr_gen_instr_val_1     = 32'h 0500_0028;
   Bit #(32) instr_reg_addr_gen_instr_val_2     = 32'h 0500_002C;
   Bit #(32) instr_reg_addr_gen_setpoint_val_0  = 32'h 0500_0030;
   Bit #(32) instr_reg_addr_gen_setpoint_val_1  = 32'h 0500_0034;
   Bit #(32) instr_reg_addr_gen_setpoint_val_2  = 32'h 0500_0038;
   Bit #(32) instr_reg_addr_gen_res             = 32'h 0500_003C;

   Bit #(32) actuation_reg_addr_gen_base        = 32'h 0500_0040; // Generated Actuation base register
   Bit #(32) actuation_reg_addr_gen_trip_0      = 32'h 0500_0044;
   Bit #(32) actuation_reg_addr_gen_trip_1      = 32'h 0500_0048;
   Bit #(32) actuation_reg_addr_gen_trip_2      = 32'h 0500_004C;
   Bit #(32) actuation_reg_addr_gen_res         = 32'h 0500_0050;

   Bit #(32) io_top_addr                        = 32'h 0500_0050;

   /**
   * ////////////////////////////////////////////////////////////////
   * IO registers
   * ////////////////////////////////////////////////////////////////
   */
   Reg #(Bit #(32)) rg_gpio <- mkReg(0);
   Reg #(Bit #(8)) rg_uart_tx <- mkReg(0);
   Reg #(Bit #(8)) rg_uart_rx <- mkReg(0);
   Reg #(Bool) rg_uart_rx_data_ready <- mkReg(False);
   Reg #(Bool) rg_uart_tx_data_ready <- mkReg(False);
   Reg #(Bit #(8)) rg_i2c_addr <- mkReg(0);
   Reg #(Bit #(32)) rg_i2c_data <- mkReg(0);
   Reg #(Bit #(32)) rg_i2c_status <- mkReg(0);
   Reg #(Bool) rg_i2c_transaction_ready <- mkReg(False);
   Reg #(Bit #(32)) rg_i2c_transaction_complete <- mkReg(0);
   Vector#(3, Reg#(Bit #(32))) instr_hand_vals <- replicateM( mkReg(0) );
   Vector#(3, Reg#(Bit #(32))) instr_hand_setpoints <- replicateM( mkReg(0) );
   Vector#(3, Reg#(Bit #(32))) instr_gen_vals <- replicateM( mkReg(0) );
   Vector#(3, Reg#(Bit #(32))) instr_gen_setpoints <- replicateM( mkReg(0) );
   Vector#(3, Reg#(Bit #(32))) actuation_trips <- replicateM( mkReg(0) );
   Reg #(Bit #(32)) rg_actuation_res <- mkReg(0);
   Reg #(Bit #(32)) rg_instr_hand_res <- mkReg(0);
   Reg #(Bit #(32)) rg_instr_gen_res <- mkReg(0);

   RWire#(Bit #(64)) rw_tick <- mkRWire();
   Reg#(Bit#(30)) rg_dmem_addr <- mkReg(0);
   Reg#(Bit#(32)) rg_dmem_put_data <- mkReg(0);

   /**
   * ////////////////////////////////////////////////////////////////
   * Memory Definition
   * ////////////////////////////////////////////////////////////////
   */
   // Memory size
   Integer imemory_size = 'h07000;
   Integer dmemory_size = 'h03000;

   // Nerv has Harward architecture (separate data and instruction memory),
   // so in order to properly initialize global symbols, we need to load
   // the hex file into *both* memories.
   // NOTE: BRAM has size defined as `reg [DATA_WIDTH-1:0]           RAM[0:MEMSIZE-1];`
   // while RegFileLoad was `reg [data_width - 1 : 0]    arr[lo:hi];`
   // The size+1 is simply to make the current hex file fit.
   BRAM_PORT#(Bit#(30), Bit#(32)) dmem_bram <- mkBRAMCore1Load(dmemory_size+1, False,"dmem_contents.memhex32", False);
   BRAM_PORT#(Bit#(30), Bit#(32)) imem_bram <- mkBRAMCore1Load(imemory_size+1, False,"imem_contents.memhex32", False);

   Reg #(Bit #(32)) rg_imem_addr  <- mkReg (0);
   Reg #(Bit #(32)) rg_imem_data  <- mkRegU;
   Reg #(Bit #(32)) rg_dmem_rdata <- mkRegU;
   Reg #(Bool) rg_update_dmem <- mkReg(False);
   Reg #(Bit #(64)) rg_tick    <- mkReg (0);
   Reg#(State) state <- mkReg(REQ_I);

   /**
   * ////////////////////////////////////////////////////////////////
   * Function definitions
   * ////////////////////////////////////////////////////////////////
   */
   function Bit #(8) strb2byte (Bit #(1) b) = signExtend (b);

   // GPIO update
   function ActionValue#(Bit#(32)) fn_gpio(Bit#(32) mask, Bit#(32) wdata)
      = actionvalue
         let gpio_val = ((rg_gpio & (~ mask)) | (wdata & mask));
         rg_gpio <= gpio_val;
         return gpio_val;
      endactionvalue;

   // GPIO update
   function ActionValue#(Bit#(32)) fn_uart(Bit#(32) addr, Bit#(32) wdata)
      = actionvalue
      case (addr)
         // Write a byte to serial port
         uart_reg_addr_tx:
            begin
               rg_uart_tx <= wdata[7:0];
               rg_uart_tx_data_ready <= True;
               return signExtend(wdata[7:0]);
            end
         // Receive data from serial port
         // Note: might be 0 or stale, check uart_reg_addr_dr first
         uart_reg_addr_rx:
            begin
               rg_uart_rx_data_ready <= False;
               return signExtend(rg_uart_rx);
            end
         uart_reg_addr_dr:
            begin
               if (rg_uart_rx_data_ready)
                  return 1;
               else
                  return 0;
            end
         default:
            return 'hFFFF;
      endcase
      endactionvalue;

   // Clock
   function Bit#(32) fn_clock(Bit#(32) addr);
      if (addr == clock_reg_adrr_lower)
         return rg_tick[31:0];
      else
         return rg_tick[63:32];
   endfunction

   /**
   * ////////////////////////////////////////////////////////////////
   * State machine
   * ////////////////////////////////////////////////////////////////
   */
   rule stateReqI (state == REQ_I); // default state
      // request a new instruction from m_imem_addr
      imem_bram.put(False, nerv.m_imem_addr [31:2], 0);
      nerv.m_stall (True); // stall CPU until the fetch is done
      rg_tick <= rg_tick + 1;
      nerv.m_dmem_rdata (rg_dmem_rdata);
      state <= PUSH_I;
   endrule

   rule statePushI (state == PUSH_I);
      // push the new instruction from the memory to the CPU
      nerv.m_imem_data (imem_bram.read());
      if (nerv.m_dmem_valid)
         state <= REQ_D;
      else
         state <= STOP;
   endrule

   rule stateReqD (state == REQ_D);
      // request data from a new data memory address
      dmem_bram.put(False, nerv.m_dmem_addr [31:2], 0);
      state <= PUSH_D;
   endrule

   rule statePushD (state == PUSH_D);
      // push new data into the CPU
      let d_addr     = nerv.m_dmem_addr;
      let mem_data = dmem_bram.read();
      let dmw      = nerv.m_get_dmem;
      let wstrb    = dmw.wstrb;
      let wdata    = dmw.wdata;
      let mask  = {strb2byte (wstrb [3]),
           strb2byte (wstrb [2]),
           strb2byte (wstrb [1]),
           strb2byte (wstrb [0])};

      let put_data = ((mem_data & (~ mask)) | (wdata & mask));
      if (show_load_store)
         $display ("DMem addr 0x%0h  wstrb 0x%0h  wdata 0x%0h mask 0x%0h put_data 0x%0h" , d_addr[31:2], wstrb, wdata, mask, put_data);

      case (d_addr)
         gpio_addr:
            put_data <- fn_gpio(mask, wdata);
         uart_reg_addr_tx, uart_reg_addr_rx, uart_reg_addr_dr:
            put_data <- fn_uart(d_addr, wdata);
         clock_reg_adrr_lower, clock_reg_adrr_upper:
            put_data = fn_clock(d_addr);
         /**
         * ////////////////////////////////////////////////////////////////
         * Regular memory read (no IO)
         * ////////////////////////////////////////////////////////////////
         */
         default:
            begin
               dmem_bram.put(True, d_addr [31:2], put_data);
            end
      endcase
      // RDATA are always updated
      rg_dmem_rdata <= put_data;
      state <= STOP;
   endrule

   rule stateStop (state == STOP);
      nerv.m_dmem_rdata (rg_dmem_rdata);
      nerv.m_stall (False); // unstall the CPU
      state <= REQ_I;
   endrule


   /**
   * ////////////////////////////////////////////////////////////////
   * Instruction memory
   * ////////////////////////////////////////////////////////////////
   */
   // This rule deals with instruction fetch and D-Mem read results
   //(* fire_when_enabled, no_implicit_conditions *)
   // rule rl_always;
   //    // let i_addr = nerv.m_imem_addr;
   //    // let imem_data = imem_bram.read();
   //    // rg_imem_addr <= i_addr;
   //    // imem_bram.put(False, i_addr [31:2], 0);

   //    // nerv.m_stall (False);
   //    // nerv.m_imem_data (imem_data);
   //    // nerv.m_dmem_rdata (rg_dmem_rdata);

   //    // if (show_exec_trace)
   //    //    $display ("%0d: PC 0x%0h  Instr 0x%0h  Next PC 0x%0h dmem_valid 0x%0h",
   //    //       rg_tick, rg_imem_addr, imem_data, i_addr, nerv.m_dmem_valid);

   //    // TODO: this will be wrong
   //    rg_tick <= rg_tick + 1;
   //    rw_tick.wset(rg_tick);
   // endrule

   /**
   * ////////////////////////////////////////////////////////////////
   * Data memory
   * ////////////////////////////////////////////////////////////////
   */
   // This rule deals with D-Mem writes and IO writes
   // rule rl_memop(nerv.m_dmem_valid);
   //    case (d_addr)
   //       /**
   //       * ////////////////////////////////////////////////////////////////
   //       * GPIO write
   //       * ////////////////////////////////////////////////////////////////
   //       */
   //       gpio_addr:
   //          begin
   //             // GPIO update
   //             let gpio_val = ((rg_gpio & (~ mask)) | (wdata & mask));
   //             rg_gpio <= gpio_val;
   //             rg_dmem_rdata <= gpio_val;
   //          end
   //       /**
   //       * ////////////////////////////////////////////////////////////////
   //       * UART
   //       * ////////////////////////////////////////////////////////////////
   //       */
   //       // Write a byte to serial port
   //       uart_reg_addr_tx:
   //          begin
   //                rg_uart_tx <= wdata[7:0];
   //                rg_uart_tx_data_ready <= True;
   //          end
   //       // Receive data from serial port
   //       // Note: might be 0 or stale, check uart_reg_addr_dr first
   //       uart_reg_addr_rx:
   //          begin
   //                rg_dmem_rdata <= signExtend(rg_uart_rx);
   //                rg_uart_rx_data_ready <= False;
   //          end
   //       uart_reg_addr_dr:
   //          begin
   //                if (rg_uart_rx_data_ready)
   //                rg_dmem_rdata <= 1;
   //                else
   //                rg_dmem_rdata <= 0;
   //          end
   //       /**
   //       * ////////////////////////////////////////////////////////////////
   //       * I2C
   //       * ////////////////////////////////////////////////////////////////
   //       */
   //       i2c_reg_addr_base:
   //          begin
   //             // Only 8 bytes for the address, the rest is ignored
   //             rg_i2c_addr <= wdata[7:0];
   //             rg_i2c_transaction_ready <= True;
   //          end
   //       i2c_reg_addr_data:
   //          begin
   //             if (mask == 0)
   //             begin
   //                // Read rg_i2c_data
   //                rg_dmem_rdata <= rg_i2c_data;
   //             end
   //             else
   //             begin
   //                // Write to rg_i2c_data
   //                rg_i2c_data <= wdata;//((rg_i2c_data & (~ mask)) | (wdata & mask));
   //             end
   //          end
   //       i2c_reg_addr_stat:
   //          begin
   //             rg_dmem_rdata <= rg_i2c_transaction_complete;
   //             rg_i2c_transaction_complete <= 0;
   //          end
   //       /**
   //       * ////////////////////////////////////////////////////////////////
   //       * Instrumentation handwritten unit
   //       * ////////////////////////////////////////////////////////////////
   //       */
   //       instr_reg_addr_hand_base:
   //          begin
   //             // wdata[0] - fnc select ( 0 - is_channel_tripped | 1 - generate_sensor_trips)
   //             // wdata[2:1] - mode
   //             // wdata[3] - sensor_tripped
   //             // rg_instr_hand_res[2:0] - result
   //             // rg_instr_hand_res[31] - fnc select ( 0 - is_channel_tripped | 1 - generate_sensor_trips)
   //             if (wdata[0] == 0)
   //                begin
   //                   // is_channel_tripped
   //                   // method Bool is_channel_tripped (Bit #(2) mode, Bool sensor_tripped);
   //                   let mode = wdata[2:1];
   //                   let sensor_tripped = unpack(wdata[3]);
   //                   rg_instr_hand_res <= signExtend( pack(instr_hand.channel.is_channel_tripped(mode, sensor_tripped)) );
   //                end
   //             else
   //                begin
   //                   // generate_sensor_trips
   //                   Vector#(3, Bit#(32)) vals = newVector;
   //                   vals[0] = instr_hand_vals[0];
   //                   vals[1] = instr_hand_vals[1];
   //                   vals[2] = instr_hand_vals[2];

   //                   Vector#(3, Bit#(32)) setpoints = newVector;
   //                   setpoints[0] = instr_hand_setpoints[0];
   //                   setpoints[1] = instr_hand_setpoints[1];
   //                   setpoints[2] = instr_hand_setpoints[2];

   //                   let res = signExtend(pack(
   //                               instr_hand.sensors.generate_sensor_trips(vals, setpoints)
   //                            ));
   //                   res[31] = 1;
   //                   rg_instr_hand_res <= res;
   //                end
   //          end
   //       instr_reg_addr_hand_instr_val_0:
   //          begin
   //             instr_hand_vals[0] <= ((instr_hand_vals[0] & (~ mask)) | (wdata & mask));
   //          end
   //       instr_reg_addr_hand_instr_val_1:
   //          begin
   //             instr_hand_vals[1] <= ((instr_hand_vals[1] & (~ mask)) | (wdata & mask));
   //          end
   //       instr_reg_addr_hand_instr_val_2:
   //          begin
   //             instr_hand_vals[2] <= ((instr_hand_vals[2] & (~ mask)) | (wdata & mask));
   //          end
   //       instr_reg_addr_hand_setpoint_val_0:
   //          begin
   //             instr_hand_setpoints[0] <= ((instr_hand_setpoints[0] & (~ mask)) | (wdata & mask));
   //          end
   //       instr_reg_addr_hand_setpoint_val_1:
   //          begin
   //             instr_hand_setpoints[1] <= ((instr_hand_setpoints[1] & (~ mask)) | (wdata & mask));
   //          end
   //       instr_reg_addr_hand_setpoint_val_2:
   //          begin
   //             instr_hand_setpoints[2] <= ((instr_hand_setpoints[2] & (~ mask)) | (wdata & mask));
   //          end
   //       instr_reg_addr_hand_res:
   //          begin
   //             rg_dmem_rdata <= rg_instr_hand_res;
   //          end
   //       /**
   //       * ////////////////////////////////////////////////////////////////
   //       * Instrumentation generated unit
   //       * ////////////////////////////////////////////////////////////////
   //       */
   //       instr_reg_addr_gen_base:
   //          begin
   //             // wdata[0] - fnc select ( 0 - is_channel_tripped | 1 - generate_sensor_trips)
   //             // wdata[2:1] - mode
   //             // wdata[3] - sensor_tripped
   //             // rg_instr_gen_res[2:0] - result
   //             // rg_instr_gen_res[31] - fnc select ( 0 - is_channel_tripped | 1 - generate_sensor_trips)
   //             if (wdata[0] == 0)
   //                begin
   //                // is_channel_tripped
   //                // method Bool is_channel_tripped (Bit #(2) mode, Bool sensor_tripped);
   //                let mode = wdata[2:1];
   //                let sensor_tripped = unpack(wdata[3]);
   //                rg_instr_gen_res <= signExtend(pack(
   //                                     instr_gen.channel.is_channel_tripped(mode, sensor_tripped)
   //                                     ));
   //                end
   //             else
   //                begin
   //                   // generate_sensor_trips
   //                   Vector#(3, Bit#(32)) vals = newVector;
   //                   vals[0] = instr_gen_vals[0];
   //                   vals[1] = instr_gen_vals[1];
   //                   vals[2] = instr_gen_vals[2];

   //                   Vector#(3, Bit#(32)) setpoints = newVector;
   //                   setpoints[0] = instr_gen_setpoints[0];
   //                   setpoints[1] = instr_gen_setpoints[1];
   //                   setpoints[2] = instr_gen_setpoints[2];
   //                   let res = signExtend(pack(
   //                               instr_gen.sensors.generate_sensor_trips(vals, setpoints)
   //                            ));
   //                   res[31] = 1;
   //                   rg_instr_gen_res <= res;
   //                end
   //          end
   //       instr_reg_addr_gen_instr_val_0:
   //          begin
   //             instr_gen_vals[0] <= ((instr_gen_vals[0] & (~ mask)) | (wdata & mask));
   //          end
   //       instr_reg_addr_gen_instr_val_1:
   //          begin
   //             instr_gen_vals[1] <= ((instr_gen_vals[1] & (~ mask)) | (wdata & mask));
   //          end
   //       instr_reg_addr_gen_instr_val_2:
   //          begin
   //             instr_gen_vals[2] <= ((instr_gen_vals[2] & (~ mask)) | (wdata & mask));
   //          end
   //       instr_reg_addr_gen_setpoint_val_0:
   //          begin
   //             instr_gen_setpoints[0] <= ((instr_gen_setpoints[0] & (~ mask)) | (wdata & mask));
   //          end
   //       instr_reg_addr_gen_setpoint_val_1:
   //          begin
   //             instr_gen_setpoints[1] <= ((instr_gen_setpoints[1] & (~ mask)) | (wdata & mask));
   //          end
   //       instr_reg_addr_gen_setpoint_val_2:
   //          begin
   //             instr_gen_setpoints[2] <= ((instr_gen_setpoints[2] & (~ mask)) | (wdata & mask));
   //          end
   //       instr_reg_addr_gen_res:
   //          begin
   //             rg_dmem_rdata <= rg_instr_gen_res;
   //          end
   //       /**
   //       * ////////////////////////////////////////////////////////////////
   //       * Actuation unit
   //       * ////////////////////////////////////////////////////////////////
   //       */
   //       actuation_reg_addr_gen_base:
   //          begin
   //             // base - trigger the actuation
   //             Bool old = unpack(wdata[0]);
   //             Vector#(3, Bit#(32)) trips = newVector;
   //             trips[0] = actuation_trips[0];
   //             trips[1] = actuation_trips[1];
   //             trips[2] = actuation_trips[2];
   //             // wdata[0] - value of `old` argument
   //             // wdata[1] - which actuator to actuate
   //             if (wdata[1] == 0)
   //                begin
   //                   // Actuate D0
   //                   rg_actuation_res <= signExtend( pack(actuation_gen.d0.actuate_d0(trips, old)) );
   //                end
   //             else
   //                begin
   //                   // Actuate D1
   //                   rg_actuation_res <= signExtend( pack(actuation_gen.d1.actuate_d1(trips, old)) );
   //                end
   //          end
   //       actuation_reg_addr_gen_trip_0:
   //          begin
   //             // Set value for trip value 0
   //             actuation_trips[0] <= ((actuation_trips[0] & (~ mask)) | (wdata & mask));
   //          end
   //       actuation_reg_addr_gen_trip_1:
   //          begin
   //             // Set value for trip value 1
   //             actuation_trips[1] <= ((actuation_trips[1] & (~ mask)) | (wdata & mask));
   //          end
   //       actuation_reg_addr_gen_trip_2:
   //          begin
   //             // Set value for trip value 2
   //             actuation_trips[2] <= ((actuation_trips[2] & (~ mask)) | (wdata & mask));
   //          end
   //       actuation_reg_addr_gen_res:
   //          begin
   //             // Get actuation results
   //             rg_dmem_rdata <= rg_actuation_res;
   //          end
   //       /**
   //       * ////////////////////////////////////////////////////////////////
   //       * Default (no IO)
   //       * ////////////////////////////////////////////////////////////////
   //       */
   //       default:
   //          begin
   //             // Regular memory read
   //             //dmem.upd (d_addr [31:2], ((mem_data & (~ mask)) | (wdata & mask)));
   //             //dmem_bram.put(True, d_addr [31:2], put_data);
   //             rg_dmem_rdata <= mem_data;
   //             rg_dmem_put_data <= put_data;
   //             rg_dmem_addr <= d_addr [31:2];
   //             if (show_load_store)
   //                $display ("rl_memop addr 0x%0h  data 0x%0h", d_addr [31:2], put_data);
   //          end
   //    endcase
   // endrule

   /**
   * ////////////////////////////////////////////////////////////////
   * Terminate if trapped
   * ////////////////////////////////////////////////////////////////
   */
   rule trap;
      if (nerv.m_trap)
      begin
         $display ("Trapped");
         $finish(0);
      end
   endrule

   /**
   * ////////////////////////////////////////////////////////////////
   * SOC Interface
   * ////////////////////////////////////////////////////////////////
   */
   // set GPIO
   method Bit #(32) gpio = rg_gpio;

   // TX -> a byte to be send
   method ActionValue#(Bit #(8)) get_uart_tx_byte () if (rg_uart_tx_data_ready);
      begin
         rg_uart_tx_data_ready <= False;
         return rg_uart_tx;
      end
   endmethod

   // Rx -> a byte to be received
   method Action set_uart_rx_byte(Bit #(8) rx);
      begin
         rg_uart_rx_data_ready <= True;
         rg_uart_rx <= rx;
      end
   endmethod

   // I2C methods
   method ActionValue #(I2CRequest) i2c_get_request () if (rg_i2c_transaction_ready);
      begin
         let r =  I2CRequest {
               write: unpack(rg_i2c_addr[0]),
               address: rg_i2c_addr[7:0], // Unclear what this is for
               slaveaddr: rg_i2c_addr[7:1],
               data: rg_i2c_data[7:0]
            };
         rg_i2c_transaction_ready <= False;
         return r;
      end
   endmethod

   method Action i2c_give_response(I2CResponse r);
      begin
         rg_i2c_data <= signExtend(r.data);
         rg_i2c_transaction_complete <= 1;
      end
   endmethod
endmodule

// ================================================================

endpackage
