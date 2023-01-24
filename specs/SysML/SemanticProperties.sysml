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

/** Semantic properties are annotation to model and system artifacts
    used to semantically markup those artifacts for documentation,
    traceability, and more. */
package 'Semantic Properties' {
  doc /* Semantic Properties are used to document arbitrary
         constructs in our specifications and implementations.
         @see https://www.kindsoftware.com/documents/whitepapers/code_standards/properties.html
       */
  import ScalarValues::*;

  /* @todo kiniry The scope of every attribute needs to be tightened. */

  attribute def <SP> 'Semantic Property';
  attribute def <SPD> 'Semantic Property with Description' :>
    'Semantic Property' {
    attribute description: String;
  }
  attribute def Exception :> String;

  package 'Meta-Information' {
    attribute def Author :> SP {
      author: String;
    }
    attribute def Lando :> SP {
      summary: String;
    }
    attribute def Bug :> SPD;
    attribute def Copyright :> SP {
      copyright: String;
    }
    attribute def Description :> SPD;
    attribute def History :> SPD;
    attribute def License :> SP {
      license: String;
    }
    attribute def Title :> SP {
      title: String;
    }
  }

  attribute def 'Author Description Scope Triple' :> SPD {
    import 'Meta-Information'::*;
    attribute author: Author;
    attribute scope: Boolean;
  }
  package 'Pending Work' {
    attribute def Idea :> 'Author Description Scope Triple' {
      classifier: String;
    }
    attribute def Review :> 'Author Description Scope Triple';
    attribute def Todo :> 'Author Description Scope Triple';
  }

  attribute def 'Rich Assertion' :> SPD {
    attribute label: String;
    attribute expression: Boolean;
    attribute exception : Exception;
  }

  attribute def 'Expression Description Pair' :> SPD {
    attribute expression: Boolean;
  }

  package 'Formal Specifications' {
    import Collections::*;
    enum def 'Modifies Frame' {
      SINGLE_ASSIGNMENT;
      QUERY;
      EXPRESSION;
    }
    attribute def Ensures :> 'Rich Assertion';
    attribute def Generate :> 'Expression Description Pair';
    attribute def Invariant :> 'Expression Description Pair' {
      exception: Exception;
    }
    attribute def Modify :> 'Expression Description Pair' {
      enum kind: 'Modifies Frame';
    }
    attribute def requires :> 'Rich Assertion';
  }

  package 'Concurrency Control' {
    import Collections::*;
    attribute def Locks :> Set;
    attribute def Timeout {
      attribute timeout: Natural;
      attribute exception: String;
    }
    attribute def 'Concurrency Semantic Property' :> 'Semantic Property' {
      attribute locks: Locks;
      attribute failure: Exception;
      attribute atomic: Boolean;
      attribute special: String;
      attribute timeout: Timeout;
    }
    attribute def Concurrent :> 'Concurrency Semantic Property' {
      attribute threadcountlimit: Positive;
      attribute broken: Boolean;
    }
    attribute def Sequential :> 'Concurrency Semantic Property';
    attribute def Guarded :> 'Concurrency Semantic Property' {
      attribute semaphore_count: Positive;
    }
  }

  package 'Usage Information' {
    attribute def 'Parameter Spec' {
      parameter_name: String;
      precondition: Boolean;
      description: String;
    }
    attribute def Return :> String;
    attribute def Exception :> 'Expression Description Pair' {
      exception: Exception;
    }
  }

  package Versioning {
    attribute def Version :> String;
    attribute def Deprecated :> String;
    attribute def Since :> String;
  }

  attribute def 'Feature Name Description Pair' {
    feature_name: String;
    description: String;
  }
  package Inheritance {
    attribute def Hides :> 'Feature Name Description Pair';
    attribute def Overrides :> 'Feature Name Description Pair';
  }

  package Documentation {
    attribute def Design :> 'Author Description Scope Triple';
    attribute def Equivalent :> String;
    attribute def Example :> String;
    attribute def See :> String;
  }

  package Dependencies {
    import Collections::*;
    attribute def References :> 'Expression Description Pair';
    // Note that we rename 'use' to 'uses' to avoid SysML keyword conflict.
    attribute def Uses :> 'Expression Description Pair';
  }

  package Miscellaneous {
    attribute def Guard :> 'Expression Description Pair';
    attribute def Values :> 'Expression Description Pair';
    attribute def 'Time Complexity' :> 'Expression Description Pair';
    attribute def 'Space Complexity' :> 'Expression Description Pair';
  }
}
