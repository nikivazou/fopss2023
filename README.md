# fopss2023 Liquid Haskell Lecture 

# Installation

```
git clone git@github.com:nikivazou/fopss2023.git
cd fopss2023/intro
stack install 
```

# Outline 
### Lecture I: Liquid Haskell Overview  
### Lecture II: Resource Analysis with RTick 
### Lecture III: Theorem Proving 


# Lecture I: Liquid Haskell Overview  
## Intro.lhs: Description of simple refinement types that encode pre- and post-conditions to avoid division by zero.  
## List.lhs: Description of Measures and standard program properties, i.e., termination and totality.   
## SortedList.lhs: Description of refinements on data types to encode inductive properties, like sortedness. 
### Extra verifies sorting algorithms: InsertSort.lhs, MergeSort.lhs, GHCSort.lhs.  
## ListTheorems.lhs: is an intro to theorem proving potential of Liquid Haskell that proves associativity and distributivity of list append. 

# Lecture II: Resource Analysis with RTick
### `RTick.hs` library definition 
### `ISort.hs` insertion sort with bound 
### `ISortLazy.hs` insertion sort on lazy lists 
### `ISortSorted.hs` prove relational theorem on isort 

# Lecture III: Theorem Proving 

