// Copyright 2020-2022 F4PGA Authors
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
//
// SPDX-License-Identifier: Apache-2.0


module inv (
    output Q,
    input  A
);
  assign Q = A ? 0 : 1;
endmodule

module buff (
    output Q,
    input  A
);
  assign Q = A;
endmodule

module logic_0 (
    output a
);
  assign a = 0;
endmodule

module logic_1 (
    output a
);
  assign a = 1;
endmodule

(* blackbox *)
module gclkbuff (
    input  A,
    output Z
);

  assign Z = A;

endmodule

