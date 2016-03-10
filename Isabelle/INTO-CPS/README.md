# INTO-CPS
This contains the application of FRAGMENTA in the INTO-CPS project.

This INTO-SysML profile and several INTO-SysML models are represented in FRAGMENTA, providing
a machine-, proof-, and Isabelle-amenable representation of INTO-SysML models.

The approach is illustrated in a very practical setting: detection of algebraic loops in INTO-SysML models. It is as follows:
* CSP models are generated from INTO-SysML models, using Isabelle, based on the FRAGMENTA representation.
* Algebraic loops are detected from the CSP model by checking, using the FDR3 refinement checker, a traces refinement assertion.

The following files can be run in Isabelle 2016 to generate the CSP files:
* 'INTO_SysML_3WTs_toCSP.thy' generates the CSP for a simplified version of the three water tanks system, which includes a version of 3 water tanks with an algebraic loop.
* 'INTO_SysML_3WTsPilot_toCSP.thy' generates the CSP for the pilot version of the INTO-CPS "3 Water Tanks" case study. 
* The generated CSPm files are available in the CSP folder.
