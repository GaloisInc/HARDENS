/*
 Copyright 2021, 2022, 2023 Galois, Inc.

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
*/

/**
 * The set of all atomic external or internal actions that the RTS
 * system can take.  Note that every scenario must be describable by
 * a sequence of actions.
 */
package <Actions> 'RTS Actions' {
  package <Internal> 'RTS Internal Actions' {
    action def <IA> 'Internal Action' {
      doc /* Actions internal to the RTS */
    }
    action <Trip> 'Signal Trip' : IA {
      in item division;
      in item channel;
    }
    action <Vote> 'Vote on Like Trips using Two-out-of-four Coincidence' : IA {
      in item divisions[2];
      in item channel;
    }
    action <A> 'Automatically Actuate Device' : IA {
      in item device;
    }
    action <T> 'Self-test of Safety Signal Path' : IA;
  }
  package <External> 'RTS External Actions' {
    package 'UI Actions' {
      action def <UIA> 'UI Action' {
        doc /* Actions exhibited by the RTS UI, either inbound or outbound. */
      }
      // @design kiniry These should both be specializations of UIA, but I
      // don't know how to write that in SysML yet.
      action def <UI_IA> 'UI Input Action';
      action def <UI_OA> 'UI Output Action';

      // Input actions.
      // @todo kiniry Add features to correspond to UI parameters.
      action <A> Actuate : UI_IA {
        in item actuator;
        in item on_off;
      }
      action <M> 'Set Maintenance Mode' :  UI_IA {
        in item division;
        in item on_off;
      }
      action <B> 'Set Mode' : UI_IA {
        in item division;
        in item trip_mode;
      }
      action <S> 'Set Setpoint' : UI_IA {
        in item division;
        in item channel;
        in item value;
      }
      action <V> 'Sensor Value' : UI_IA {
        doc /* Simulate a sensor reading */
        in item division;
        in item channel;
        in item value;
      }
      action <Q> 'Quit' : UI_IA;

      // Output actions.
      action 'Display Pressure' : UI_OA;
      action 'Display Temperature' : UI_OA;
      action 'Display Saturation Margin': UI_OA;
      action 'Display Trip Ouput Signal State': UI_OA;
      action 'Display Indication Of Channel in Bypass': UI_OA;
      action 'Display Actuation State': UI_OA;
    }
  }
}