# Introduction

This libary attempts to provied Array programing inspiered by APL-family languagess in idris2, by employing dependet typing to elimate comes sources of error usually encountert in this model of programing.

## Arrays in APL-family languages

In the clasic model we define Arrays by two characteristics: 
- the Shape, a simple Vector defining the lenght of each dimension. For example a simple Vector with 5 elements is of Shape [5], a 2x3 Matrix of Shape [2,3].
- the Ravel, which contains all Elements of the Array in a simple Vector. For example the ravel of a 2x2 Matrix and a Vector of lenght 4 could be identical.

From those characteristics, we can derive other properties of the Array:
- The Rank, the lenght of the Shape
- The Bound, the number of elements in the Array, thus the lenght of the Ravel and the product of the Shape.

Traditionaly APL-like languages are dynamicly typed and permit multiple different types in each Array, usually thes are numbers (often a subset of Integers,Nats,Complex Numbers,Doubles,Floats), Characters, and Strings, which may or may not defined as Arrays of Chars. 

## Arrays in Idris2

By using the static type system of Idris2 we must change the approach to the Array data type:
The two primary characteristics of the Array are now formaliesed at the typelevel:

1. The Shape now indexes the Array type, represented as List of Nats.
2. The Ravels type is now parameteising the Array, and therfore prevents the usage of Arrays with heterogenous type. We store the Ravel as a Idris vector, indexed by its length, which is equal to the product of the Shape.

Because there are multiple possible Shapes with a product equal to the length of a given Array it is always necessay to supply the Shape for each Array, this complicates usage in the repl.

### Implemented Functions:

Basic Functions to retrive or calculate the properties of Arrays were easily implemeted in Idris2, and helped along by the usage of implicit Argumenrs to retrive the typelevel Shape in a function, and by existing functions on Lists and Vectors.

The pointwise Function, which is functional equal to map, simply used the map implementaion on Vectors to map a function over the ravel of a Array.

For the slightly more complicated function eachF, which applies a Array of functions on a Array of appropiate data and equal length, the type system can ensure that those properties are actually correct.

The related function eachD, which combines two arrays of equal Shape in a Array with a additional dimension of length 2, by replaceing each element in the first Array with itself and the appropiate element in the second Array (this is comparable to zipping the last dimensions of the Arrays) used the implicit and auto features of Idris2, which automaticly can prof that the Shape of the new Array is correct.

For the concatenate function, which appends the first dimension of two Arrays (e.g. turning a 2x2 and a 3x2 Matrix into a 5x2 Matrix), the same auto techninque proofs the resulting shape to be corect.

### Problems

Acessing the elements of this kind of Array in a staticly typed and safe way turned out complicated:
To prevent out of bound errors a special Data type Index, indexd by a Shape, is used.
This type consists of a List of Nats strictly lower than the lenght of the Shape in the appropiate dimensions, it should additionaly ensure the length of the Index to be equal to the Rank. 
Unfourtunatly using this type to calculate the postion of a Index as the position of the approiate element in the Ravel, proofed to complicated for this project.
This was mainly caused by greated difficultys in the usage of the Fin (Finite Set) base libary of Idris2, which was used in the implementaion of the Index type, to ensure the Index to conform to the Shape. The greatest problem here was arithmic with the Fin type.

### Further work and ideas

Two features of APL-like languages which appear to be possilbe, but very difficult, to implemnt in Idris2 are:
1. The possiblity to have heterogenous Arrays, possible by using the HVect libary to replace the Ravel Vector with a heterogenus Vector. 
   This would lead to Arrays indexed not just by a Shape but also by a Vector of Types with the lenght of the prouct of the Shape.
   Unfourtunatly this would result in immens difficultys in typecheking and would need a generic dispatch mechanism for functions, else we would need to specifiy a fitting function for every singel element for many useful APL functions, for example to fillter a Array (e.g. one equality check for Nats, one for Chars, one for Integers, ...).
   In addition we would need to define the type of every singel Element of a HVect.
   To be truly useful we would need to be able to:
   - create a HVect like type without the requirment to define every single Type, for example by creating a Union-Type which supplys all possible types of the Vector.
   - create a dipatcher to select the correct function for every element of a vector
   - get it to typechecke :(
   In some experimataion this has proven to be far to wide a scope.
   Alternativly we could use a Sum Type containing all types we want to used in a Array, this would not requier the use of HVects anymore, but we would need to always define a new Sum Type to use an Array with a new combination of types.
2. The APL model of dyadic and monadic functions, which permit "function trains", a simple way to compose functions in a flexible ways.
   A implementaion could use the Arrow libary for Idris2, which apperas a good fit (Arrows, just like idris functions have either one,tow, or no input), this libary descibes a Model of combutation which apperas to fit well to descrieb classic APL programing.
   Another approach, for which some experimataion exists in "ideenUndVorgabe/ideen.idr" is to greate a Data types for monadic and dyadic functions and wrappers for a single or two arguments, and than create a interface for these.
   Unfourtunatly this apperas to requier a great amount of wrapper types and a dispatch function to correctly used monadic functions only on monadic arguments and dyadic functions on dyadic arguments, we would also need to define every function with a wrapper, containing the possible monadic and/or dyadic version of the function.
