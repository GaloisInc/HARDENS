/**
 * The IEEE 603-2018 requirements (known as "characteristics" in
 * the standard) which the RTS demonstrator system must fulfill.
 */
package id Characteristics 'IEEE Std 603-2018 Characteristics' {
  requirement def 'Requirements Consistency' {
    doc /* Requirements must be shown to be consistent. */
  }
  requirement def 'Requirements Colloquial Completeness' {
    doc /* The system must be shown to fulfill all requirements. */
  }
  requirement def 'Requirements Formal Completeness' {
    doc /* Requirements must be shown to be formally complete. */
  }
  requirement def 'Instrumentation Independence' {
    doc /* Independence among the four divisions of instrumentation (inability
           for the behavior of one division to interfere or adversely affect the
           performance of another). */
  } 
  requirement def 'Channel Independence' {
    doc /* Independence among the two instrumentation channels within a division
           (inability for the behavior of one channel to interfere or adversely
           affect the performance of another). */
  }
  requirement def 'Actuation Independence' {
    doc /* Independence among the two trains of actuation logic (inability for
           the behavior of one train to interfere or adversely affect the
           performance of another). */
  }
  requirement def 'Actuation Correctness' {
    doc /* Completion of actuation whenever coincidence logic is satisfied or
           manual actuation is initiated. */
  }
  requirement def 'Self-Test/Trip Independence' {
    doc /* Independence between periodic self-test functions and trip functions
           (inability for the behavior of the self-testing to interfere or
           adversely affect the trip functions). */
  }
}
