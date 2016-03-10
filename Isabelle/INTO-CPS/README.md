# INTO-CPS
This contains the application of FRAGMENTA in the INTO-CPS project.

This INTO-SysML profile and several INTO-SysML models are represented in FRAGMENTA, providing
a machine-, proof-, and Isabelle-amenable representation of INTO-SysML models.

The approach is illustrated in a very practical setting: detection of algebraic loops in INTO-SysML models.
This is done by a generation into CSP from an INTO-SysML model; the detection is done using the FDR3 refinement checker by  checking a traces refinement assertion.

From INTO-SysML models we generate, using FRAGMENTA's facilities, the corresponding CSPm files (the generated CSPm files are available in the CSP folder).
