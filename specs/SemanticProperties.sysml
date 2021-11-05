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
  /* @todo kiniry Many properties' types must be refined. */

  attribute def AuthorDescription {
    attribute author: String;
    attribute description: String;
    attribute scope: Boolean;
  }

  package 'Meta-Information' {
    attribute author: String;
    attribute lando: String;
    attribute bug: String;
    attribute copyright: String;
    attribute description: String;
    attribute history: String;
    attribute license: String;
    attribute title: String;
  }

  package 'Pending Work' {
    /** @todo to be refined according to definition */
    attribute idea: String;
    attribute review: String;
    attribute todo: String;
  }

  private item def RichAssertion {
    attribute label: String;
    attribute expression: Boolean;
    // attribute exception: Exception/Signal;
    attribute description: String;
  }

  private item def ExpressionDescriptionPair {
    attribute expression: Boolean;
    attribute definition: String;
  }
    
  enum def ModifiesFrame {
    SINGLE_ASSIGNMENT;
    QUERY;
    EXPRESSION;
  }
  package 'Formal Specifications' {
    attribute ensures: Boolean;
    attribute generate: Boolean;
    attribute invariant: Boolean;
    attribute modify: Boolean;
    attribute requires: Boolean;
  }
    
  package 'Concurrency Control' {
    attribute concurrency: Boolean;
  }
    
  package 'Usage Information' {
    attribute param: Boolean;
    // Note that we rename 'return' to 'result' to avoid SysML keyword conflict.
    attribute result: Boolean;
    attribute exception: Boolean;        
  }
    
  package Versioning {
    attribute version: String;
    attribute deprecated: String;
    attribute since: String;
  }
    
  package Inheritance {
    attribute hides: String;
    attribute overrides: String;
  }
    
  package Documentation {
    attribute design: String;
    attribute equivalent: Boolean;
    attribute example: String;
    attribute see: String;
  }
    
  package Dependencies {
    attribute references: Boolean;
    // Note that we rename 'use' to 'uses' to avoid SysML keyword conflict.
    attribute uses: Boolean;
  }
    
  package Miscellaneous {
    attribute guard: Boolean;
    attribute vales: Boolean;
    attribute time_complexity: Boolean;
    attribute space_complexity: Boolean;
  }
}
