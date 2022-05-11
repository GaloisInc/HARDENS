/**
 * The set of all atomic external or internal actions that the RTS
 * system can take.  Note that every scenario must be describable by
 * a sequence of actions. 
 */
package id Actions 'RTS Actions' {
  package id Internal 'RTS Internal Actions' {
    action def id IA 'Intenral Action' {
      doc /* Actions internal to the RTS */
    }
    action id Trip 'Signal Trip' : IA {
      in item division;
      in item channel;
    }
    action id Vote 'Vote on Like Trips using Two-out-of-four Coincidence' : IA {
      in item divisions[2];
      in item channel;
    }
    action id A 'Automatically Actuate Device' : IA {
      in item device;
    }
    action id T 'Self-test of Safety Signal Path' : IA;
  } 
  package id External 'RTS External Actions' {
    package 'UI Actions' {
      action def id UIA 'UI Action' {
        doc /* Actions exhibited by the RTS UI, either inbound or outbound. */
      }
      // @design kiniry These should both be specializations of UIA, but I
      // don't know how to write that in SysML yet.
      action def id UI_IA 'UI Input Action';
      action def id UI_OA 'UI Output Action';
      
      // Input actions.
      // @todo kiniry Add features to correspond to UI parameters.
      action id A Actuate : UI_IA {
        in item actuator;
        in item on_off;
      }
      action id M 'Set Maintenance Mode' :  UI_IA {
        in item division;
        in item on_off;
      }
      action id B 'Set Mode' : UI_IA {
        in item division;
        in item trip_mode; 
      } 
      action id S 'Set Setpoint' : UI_IA {
        in item division;
        in item channel;
        in item value;
      }
      action id V 'Sensor Value' : UI_IA {
        doc /* Simulate a sensor reading */
        in item division;
        in item channel;
        in item value;
      }
      action id Q 'Quit' : UI_IA;
      
      // Output actions.
      action id 'Display Pressure' : UI_OA;
      action id 'Display Temperature' : UI_OA;
      action id 'Display Saturation Margin': UI_OA;
      action id 'Display Trip Ouput Signal State': UI_OA;
      action id 'Display Indication Of Channel in Bypass': UI_OA;
      action id 'Display Actuation State': UI_OA;
    }
  }
}