# FRAGMENTA

FRAGMENTA [1, 2], a theory of graphical data modelling enabling the construction of overall data or class models as fragmented sub-models. It can be used to model general purpose data models in what is known as conceptual modelling, or DSLs whose structure is defined by metamodels. It is, essentially, a data modelling theory with advanced means for separations of concerns, graphical expressiveness and healthiness checking with a mathematical underpinning.

Using FRAGMENTA, designers can break an overall model into independent sub-models (called fragments) that can be put together to build meaningful wholes. This is in contrast with more classical MDE approaches that are essentially monolithic. The theory is based on an algebraic description of models and fragments based on graphs and morphisms.

FRAGMENTA's new version is given in [1], which upgrades the version given in [2,4] and applied in [3].

This is the repository of FRAGMENTA. It includes:
* The paper presented at Models 2015 and the technical report that presents the previous version of the theory (under '/docs').
* The complete Z specification of FRAGMENTA (under 'Z-Spec'), which includes the new version of Fragmenta.
* The Isabelle files that define 'FRAGMENTA' (under 'Isabelle').
* The Haskell implementation (under 'Haskell').

## References
1. Nuno Amálio. *Enhancing Expressivity, Modularity and Rigour of Graphical Data Modelling with Fragmenta*. To be published in ACM TOSEM. 2025.
2. Nuno Amálio, Juan de Lara and Esther Guerra. [*FRAGMENTA: A Theory of Fragmentation for MDE*. Models 2015.](docs/MODELS2015-article.pdf). Models 2015.
3. Nuno Amálio, Juan de Lara and Esther Guerra. [*Fragmenta: a theory of separation to design fragmented MDE models*](docs/fragmenta-tr.pdf). Technical Report. Universidad Autónoma de Madrid. 2014
4. Nuno Amálio, Richard Payne, Ana Cavalcanti and Jim Woodcock. [*Checking SysML Models for Co-Simulation*](docs/paper-icfem2016.pdf). ICFEM 2016.
