# INTO-CPS
This folder contains the application of FRAGMENTA to the INTO-CPS project, and the support for the experiment on the comparison of approaches to the detection of algebraic loops.

The Isabelle files that are required for the experiment on the detection of algebraic loops are given in the folder 'WaterTanksn'

Everything else is related to INTO-SysML, the profile of SysML for architectural modelling developed in the setting of multi-modelling and FMI co-simualation developed in the context of the INTO-CPS project.

The metamodels of INTO-SysML and several INTO-SysML models are represented in FRAGMENTA, providing
a machine-, proof-, and Isabelle-amenable representation of INTO-SysML models.

The approach is illustrated in a very practical setting: detection of algebraic loops in INTO-SysML models. It is as follows:
* CSP models are generated from INTO-SysML models, using Isabelle, based on the FRAGMENTA representation.
* Algebraic loops are detected from the CSP model by checking, using the FDR3 refinement checker, a traces refinement assertion.

The following files can be run in Isabelle 2016 to generate CSP and Alloy files:
* '3WTs/INTO_SysML_3WTs_toCSP.thy' generates the CSP and Alloy for a simplified version of the three water tanks system, which includes a version of 3 water tanks with an algebraic loop.
* '3WTsPilot/INTO_SysML_3WTsPilot_toCSP.thy' generates the CSP and Alloy for the pilot version of the INTO-CPS "3 Water Tanks" case study. 
* The generated CSPm files are available in the CSP folder.
