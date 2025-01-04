This is a **third-party** implementation of Relational Lenses by Bohannon et al. (PODS'06) [1] and its incremental version **as of 2017** by Horn's Master thesis (University of Edinburgh) [3] in OCaml. 
The former implementation also includes some code that corresponds to the extended version [2] of the PODS paper. The latter (incremental) implementation only includes the core part and there is no interaction with database or host language.
The implementation is not endoesed by any of the authors of the above papers. Although I tried to align the implementation with the above papers, there is no guarantee in the alignment, and the author of the code is solely responsible for any deviation from the papers.
The implementation was conducted as a part of the early years of JSPS Kakenhi project [Software Foundation for Interoperability of Autonomic Distributed Data based on Bidirectional Transformation (2017-2022)](https://kaken.nii.ac.jp/en/grant/KAKENHI-PROJECT-17H06099/) to study the state of the art that time.
The purpose of making the code public is to make it citable by the papers/projects built on this implementation.
For more recent work by Horn et al., please refer to ICFP 2018 paper [4] and Horn's PhD thesis [5], and associated implementations.


[1] Aaron Bohannon, Benjamin C. Pierce, and Jeffrey A. Vaughan. 2006. Relational lenses: a language for updatable views. In Proceedings of the twenty-fifth ACM SIGMOD-SIGACT-SIGART symposium on Principles of database systems (PODS ’06). Association for Computing Machinery, New York, NY, USA, 338–347. DOI:https://doi.org/10.1145/1142351.1142399

[2] Extended version of [1] as University of Pennsylvania technical report MS-CIS-05-27. http://www.cis.upenn.edu/~bcpierce/papers/dblenses-tr.pdf

[3] Horn, Rudi, Language Integrated Incremental Relational Lenses, Master of Science by Research, 
School of Informatics, University of Edinburgh, 2017. https://project-archive.inf.ed.ac.uk/msc/20172439/msc_proj.pdf 

[4] Rudi Horn, Roly Perera, and James Cheney. 2018. Incremental relational lenses. Proc. ACM Program. Lang. 2, ICFP, Article 74 (July 2018), 30 pages. DOI: https://doi.org/10.1145/3236769

[5] Rudi Horn, Language integrated relational lenses, PhD Thesis, The University of Edinburgh, 2023. http://dx.doi.org/10.7488/era/2925
