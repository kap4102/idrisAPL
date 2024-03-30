module Main

import Data.Fin
import Data.Vect
-- import Data.HVect
import Decidable.Equality
import Data.List1
import Data.List
import Data.List.Views

main : IO ()
main = printLn "Hello World"

repeate : (n : Nat) -> Vect (S m) a -> Vect (n*(S m)) a
repeate Z x = []
repeate (S k) x = x ++ repeate k x

repeateList : (n : Nat) -> List a -> List a
repeateList Z x = []
repeateList (S k) x = x ++ repeateList k x

Shape : Type
Shape = List Nat

data Index : Shape -> Type where
  Nil : Index []
  (::) : Fin n -> Index ns -> Index (n :: ns)

namespace Array
  public export
  -- data Array : (s : Shape) -> (type : Vect (product s) Type) -> Type where
  --   Data : {s : Shape} -> {type : Vect (product s) Type} ->(d : HVect type) -> Array s type
  data Array : Shape -> Type -> Type where
    Data : {s : Shape} -> (d : Vect (product s) a) -> Array s a

  -- This i a scala value
  export
  exampleArray0 : Array [1] Double
  exampleArray0 = Data [7.0]

  -- This is a 2x2 Matrix
  export
  exampleArray1 : Array [2,2] Double
  exampleArray1 = Data [1.0, 0.0, 0.0, 1.0]

  indexToList : Index s -> List Nat
  indexToList [] = []
  indexToList (x :: xs) = (finToNat x) :: indexToList xs

  zipIndexWith : {s : Shape}
              -> {auto _ : NonEmpty s}
              -> (Nat -> Nat -> Nat)
              -> Index s
              -> (s : Shape)
              -> Maybe (List1 Nat)
  zipIndexWith f xs ys = do
   i <- List1.fromList $ indexToList xs
   s <- List1.fromList ys
   List1.fromList $ zipWith f (init i) (init s) ++ [last i]
  -- zipIndexWith f (x :: []) (y :: []) = finToNat x ::: []
  -- zipIndexWith f (x :: xs) (y :: ys) = (f (finToNat x) y ::: []) ++ zipIndexWith f xs ys

  -- More performant because only one traverse needed
  -- foldForIndex : {s : Shape}
  --             -> {auto prf1 : Maybe (Fin (plus n 0))
  --                          -> Maybe (Fin (foldl (\acc, elem => mult acc elem) 1 s))}
  --             -> Index s
  --             -> (s : Shape)
  --             -> Maybe (Fin (product s))
  -- foldForIndex (x :: []) _ = do
  --  let stepRes = finToNat x
  --  prf1 $ natToFin stepRes (product s)
  -- foldForIndex (x :: xs) (y :: ys) = do
  --   stepFin <- natToFin y (product s)
  --   nextRes <- foldForIndex xs ys
  --   let stepRes = ?s --$ x * stepFin
  --   Just $ ?l-- x * stepRes +  nextRes
  -- foldForIndex _ _ = Nothing
  -- foldForIndex : {s : Shape}
  --             -> Index s
  --             -> (s : Shape)
  --             -> Maybe (Fin (product s))
  -- foldForIndex (x :: []) _ =  do
  --  let x' = finToNat x
  --  natToFin x' (product s)
  -- foldForIndex (x :: xs) (y :: ys) = do
  --  let x' = finToNat x
  --  nextRes <- foldForIndex xs ys
  --  natToFin (x' * y + nextRes) (proudct s)
  -- foldForIndex _ _ = natToFin (product s) 0
  --
  Product : List Nat -> Nat
  Product [] = 0
  Product (x :: xs) = x * Product xs

  weaken' : Fin n -> Fin (n * (Product ns))

  mul : (n : Nat) -> {auto p : IsSucc n } -> Fin m -> Fin (m * n)
  mul 0 _ impossible
  mul (S k) FZ = FZ
  mul (S j) (FS x) = shift (S j) (mul (S j)  x)

  fplus : Fin (S n) -> Fin m -> Fin (m + n)
  fplus FZ y = weakenN n y
  fplus (FS FZ) y = ?fds_0
  fplus (FS (FS x)) y = ?fsd $ FS $ fplus (FS x) y

  foldForIndex : (s : Shape) -> {_ : NonEmpty s} -> Index s
              -> Fin (Product s)
  foldForIndex [] _ impossible
  foldForIndex (0 :: ns) (i :: is) = ?rh1_0
  foldForIndex ((S k) :: ns) (i :: is) = do
   let res = (foldForIndex ns is)
       foo = mul (Product ns) {p = ?phole} i
   fplus ?hp res
   -- plus (Product ns) (mult k (Product ns))
   -- plus (mul (Product ns) i) res

  multiply : (n : Nat) -> Fin n -> Fin (Product ns) -> Fin (n * Product ns)
  multiply 0 FZ _ impossible
  multiply 0 (FS x) _ impossible
  multiply (S k) FZ y = ?multiply_rhs_2
  multiply (S k) (FS x) y = ?multiply_rhs_3

  splitLast : (xs : List1 a) -> (List a,a)
  splitLast xs = (init xs,last xs)

  -- For a Index (x::xs) the postions in the Vect d is calculated as:
  -- 1 + (x +(x-1)* (product xs))) + ... + ((last xs) +((last xs)-1)* (product []))
  index : {s : Shape}
       -> {auto _ : NonEmpty s}
       -> Array s a
       -> (is : Index s)
       -> Maybe a
  -- index {s} (Data d) is = do
  --  n <- foldForIndex is s
  --  Just $ Vect.index n d
   -- = Left $ Vect.index (sum $ splitLast $ zipIndexWith (*) (i :: is) (n :: ns)) d

  -- exampleIndexing : Double
  -- exampleIndexing = index exampleArray1 [0, 1]

  export
  pointwise : (a -> b) -> Array s a -> Array s b
  pointwise f (Data d) = Data $ map f d

  export
  ravel : Array s a -> Vect (product s) a
  ravel (Data d) = d

  export
  bound : {s : Shape} -> Array s a -> Nat
  bound {s} (Data d) = product s

  export
  rank : {s : Shape} -> Array s _ -> Nat
  rank {s} _ = length s

  export
  shape : {s : Shape} -> Array s _ -> Shape
  shape {s} _ = s

  export
  eachFZipApp : Vect n (a -> b) -> Vect n a -> Vect n b
  eachFZipApp [] [] = []
  eachFZipApp (f :: fs) (x :: xs) = (f x) :: eachFZipApp fs xs

  export
  eachF : Array s (tA -> tW) -> Array s tA -> Array s tW
  eachF (Data fs) (Data d) = Data $ eachFZipApp fs d

  -- prf : (s : Shape)
  --     ->  (mult (foldl (\acc, elem => mult acc elem) 1 s)  2)
  --       =       (foldl (\acc, elem => mult acc elem) 1    (List.(++) s [2]))
  -- prf []        = Refl
  -- prf [x]       = Refl
  -- prf (x :: xs) = ?rhs2

  export
  zipConcat : (Vect n t) -> (Vect n t) -> (Vect (n*2) t)
  zipConcat [] [] = []
  zipConcat (x :: xs) (y :: ys) = x :: y :: zipConcat xs ys


  export
  eachD : {t : Type}
       -> {s : Shape}
       -> {auto prf : Vect (mult (foldl (\acc, elem => mult acc elem) 1 s)              2) t
                  ->  Vect       (foldl (\acc, elem => mult acc elem) 1 (List.(++) s [2])) t}
       -> {dA : Vect (product s) t}
       -> {dW : Vect (product s) t}
       -> Array s t
       -> Array s t
       -> Array (s++[2]) t
  eachD {prf} (Data dA) (Data dW) = Data $ prf $ zipConcat dA dW

  -- outerProduct :
  --             (f : tA -> tW -> t')
  --            -> Array (s++[n]) tA
  --            -> Array (s++[m]) tW
  --            -> Array (s++[n*m]) t'
  -- outerProduct f (Data dA) (Data dW) = do
  --   let fstVals = concat $ map (\a => (repeate (length dW) [a])) dA
  --       sndVals = repeate (length dA) ?dW
  --   Data $ zipWith f fstVals sndVals

  -- appendFirst : {m : Nat}
  --            -> {n : Nat}
  --            -> {s : List Nat}
  --            -> (dA : Vect (foldl (\acc, elem => mult acc elem) (plus n 0) s) a)
  --            -> (dW : Vect (foldl (\acc, elem => mult acc elem) (plus m 0) s) a)
  --            ->       Vect (foldl (\acc, elem => mult acc elem) (plus (plus n m) 0) s) a
  -- appendFirst dA dW = ?appendFirst_rhs

  export
  concatenate : {dA : Vect (product (n::s)) a}
             -> {dW : Vect (product (m::s)) a}
             -> {auto appendFirstPrf : Vect (plus (foldl (\acc, elem => mult acc elem) (plus n 0) s)
                                                  (foldl (\acc, elem => mult acc elem) (plus m 0) s)) a
                                   -> Vect (foldl (\acc, elem => mult acc elem) (plus (plus n m) 0) s) a}
             -> Array (n :: s) a
             -> Array (m :: s) a
             -> Array (n + m :: s) a
  concatenate (Data dA) (Data dW) = Data $ appendFirstPrf (dA ++ dW)
  -- In most apls catenatLast has the glyph ',', and concatenates the last axis, e.g.
  -- in exampleArray3 the 3rd Dimension of the 2x2x2 Matrix resulting in a 2x2x4 Matrix
  -- Thus the Shapes are changed by adding the last Dimensions. 
  -- For two non empty arrays both must have all the same axes,
  -- and the same lenght for all of those but the last.
  begining : List Nat -> List Nat
  begining xs with (snocList xs)
    begining [] | Empty = []
    begining (xs ++ [x]) | (Snoc x xs rec) = xs

  lastOr0 : List Nat -> Nat
  lastOr0 xs with (snocList xs)
    lastOr0 [] | Empty = 0
    lastOr0 (xs ++ [x]) | (Snoc x xs rec) = x

  concat1 : List1 (List1 a) -> List1 a
  concat1 xs = List1.foldr1 List1.(++) xs


  -- catenatLast  : {t : Type}
  --            -> {s : Shape}
  --            -> {sA : Nat}
  --            -> {sW : Nat}
  --            -> {dA : Vect ((product s) * sA) t}
  --            -> {dW : Vect ((product s) * sW) t}
  --            -> (a : Array (s ++ (sA ::: [])) t)
  --            -> (w : Array (s ++ (sW ::: [])) t)
  --            -> Array (s ++ (sW + sA ::: [])) t
    -- = Data $ ?r0 $ zipWith Vect.(++) (kSplits (product s) sW ?dW) (kSplits (product s) sA (?prfA dA))
--   -- TODO more operations

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
