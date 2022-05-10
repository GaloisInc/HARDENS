
///** The physical architecture of the HARDENS RTS demonstrator. */
package 'Physical Architecture' {
  import 'Project Glossary'::*;
  import 'RTS Hardware Artifacts'::*;

//  /** A PCB developer board used to prototype hardware. */
//  part 'HARDENS Demonstrator Board' : DevBoard;
//  /** The USB cable used to communicate the ASCII UI to/from the board. */
//  part id UI_C 'USB UI Cable' : 'USB Cable';
//  /** The USB cable used to program the board with a bitstream. */
//  part id Prog_C 'USB Programming Cable' : 'USB Cable';
//  /** The USB cable used to interact with the board in a debugger. */
//  part id Debug_C 'USB Debugging I/O Cable' : 'USB Cable';
//  // @trace #11 https://github.com/GaloisInc/HARDENS/issues/11
//  // @todo Add attributes for URL traceability.
//  part def id MPL3115A2 'SparkFun Altitude/Pressure Sensor Breakout' :>
//    PCB, 'Pressure Sensor';
//  // 4x https://www.sparkfun.com/products/11084
//  part def 'SparkFun MOSFET Power Control Kit' :> PCB, Power;
//  // 4x https://www.sparkfun.com/products/12959
//  part def id TMP102 'SparkFun Digital Temperature Sensor Breakout' :>
//   PCB, 'Temperature Sensor';
//  // 4x https://www.sparkfun.com/products/13314
//  part def 'Small Push-Pull Solenoid - 12VDC' :> 'Solenoid Actuator';
//  // 4x https://www.adafruit.com/product/412
//  part def '1N4001 Diode';
//  // 1x https://www.adafruit.com/product/755
//  /** The first of two redundant temperature sensors. */
//  part id TS1 'Temperature Sensor 1' : TMP102;
//  /** The second of two redundant temperature sensors. */
//  part id TS2 'Temperature Sensor 2' : TMP102;
//  /** The first of two redundant pressure sensors. */
//  part id PS1 'Pressure Sensor 1' : MPL3115A2;
//  /** The second of two redundant pressure sensors. */
//  part id PS2 'Pressure Sensor 2' : MPL3115A2;
//  /** The first of two redundant solenoid actuators. */
//  part id SA1 'Solenoid Actuator 1' : 'Small Push-Pull Solenoid - 12VDC';
//  /** The second of two redundant solenoid actuators. */
//  part id SA2 'Solenoid Actuator 2' : 'Small Push-Pull Solenoid - 12VDC';
//  // @todo kiniry Add ports for external connectors.
//
//  /** The computer used by a developer to interface with the demonstrator,
//      typically for driving the demonstrator's UI and programming and
//      debugging the board. */
//  part def 'Developer Machine':> Computer;
//
//  /** The fully assembled HARDENS demonstrator hardware with all component present. */
//  part id Demonstrator 'HARDENS Demonstrator';
//
//  connection def DevMachineToDevBoard {
//    end: Computer;
//    end: PCB;
//  }
//    connection: DevMachineToDevBoard connect 'Developer Machine' to Board;
}
