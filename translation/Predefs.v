Require GMu.Definitions.
Require GMuAnnot.Definitions.
Require Definitions.
Require Reduction.
Require Sequences.
Require Import TLC.LibEnv.

Module Source.
  Import GMu.Definitions.
  Include GMu.Definitions.
End Source.

Module SourceAnnot.
  Import GMuAnnot.Definitions.
  Include GMuAnnot.Definitions.
End SourceAnnot.

Module Target.
  Import Definitions.
  Include Definitions.
  Import Reduction.
  Include Reduction.
  Import Sequences.
  Include Sequences.
End Target.
