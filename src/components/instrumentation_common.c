// HARDENS Reactor Trip System (RTS)

// Copyright 2021, 2022, 2023 Galois, Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "instrumentation.h"

void instrumentation_init(struct instrumentation_state *state) {
  state->maintenance = 1;
  for (int i = 0; i < NTRIP; ++i) {
    state->mode[i] = 0;
    state->reading[i] = 0;
    state->sensor_trip[i] = 0;
    state->setpoints[i] = 0;
  }
}
