module Vorgabe

import Data.Fin
import Data.Vect

-- Additional resources:
-- http://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/aplicative.pdf
-- https://benl.ouroborus.net/papers/2012-guiding/guiding-Haskell2012.pdf

Shape : Type
Shape = List Nat

data Index : Shape -> Type where
  Nil : Index []
  (::) : Fin n -> Index ns -> Index (n :: ns)

namespace Array
  public export
  data Array : Shape -> Type -> Type where
    Data : {s : Shape} -> (d : Vect (product s) a) -> Array s a

  exampleArray0 : Array [1] Double
  exampleArray0 = Data [7.0]

  exampleArray1 : Array [2, 2] Double
  exampleArray1 = Data [1.0, 0.0, 0.0, 1.0]

  index : Array s a -> Index s -> a

  exampleIndexing : Double
  exampleIndexing = index exampleArray1 [0, 1]

  pointwise : (a -> b) -> Array s a -> Array s b

  concatenate : Array (n :: s) a -> Array (m :: s) a -> Array (n + m :: s) a

  -- TODO more operations

namespace Tensor
  public export
  data Tensor : Shape -> Type -> Type where
    Computation : {s : Shape} -> (f : Index s -> a) -> Tensor s a

  exampleTensor0 : Tensor [1] Double
  exampleTensor0 = Computation (\[i] => 7.0)

  exampleTensor1 : Tensor [2, 2] Double
  exampleTensor1 = Computation (\[i1, i2] => if i1 == i2 then 1.0 else 0.0)

  shuffle : (Index s1 -> Index s2) -> Tensor s2 a -> Tensor s1 a

  pointwise : (a -> b) -> Array s a -> Array s b

  transpose : Tensor (n :: m :: s) a -> Tensor (m :: n :: s) a

  -- TODO more operations

manifest : Tensor s a -> Array s a

delay : Array s a -> Tensor s a
