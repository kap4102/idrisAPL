import Data.Fin
import Data.Vect
import Data.List

Shape : Type
Shape = List Nat

data Index : Shape -> Type where
  Nil : Index []
  (::) : Fin n -> Index ns -> Index (n :: ns)

namespace Array
  public export
  data Array : Shape -> Type -> Type where
    Data : {s : Shape} -> (ravel : Vect (product s) a) -> Array s a

data MFun : (mXTypeFun : Type) -> (f : (x : Array mSFun mXTypeFun) -> Maybe outType) -> outType -> Type where
 MF :  (f : (x : Array mSFun mXTypeFun) -> Maybe Type) -> MFun mXTypeFun f Type

data DFun : (dXTypeFun : Type) -> (dWTypeFun : Type) -> (f : (x : Array dXs dXTypeFun) -> (w : Array dWs dWTypeFun) -> outType) -> outType -> Type where
 DF : (f : (x : Array dXs dXTypeFun) -> (w : Array dWs dWTypeFun) -> Type) -> DFun dXTypeFun dWTypeFun f Type

data Monadic : (mXType : Type) -> Type where
 MV :  (mX : Array mS mXType)
    -> Monadic mXType

data Dyadic : (dXType : Type) -> (dWType : Type) -> Type where
 DV :  (dX : Array dXS dXType)
    -> (dW : Array dWS dWType)
    -> Dyadic dXType dWTYpe

data AFun : outType -> Type where
 AF :  {outType : Type}
      -> Maybe (MFun Type mf outType)
      -> Maybe (DFun Type Type df outType)
      -> AFun outType

findMOutType : (mOutType : Type)
            -> (funType : (MFun  mXTypeFun mf mOutType))
            -> Type
findMOutType mOutType funType = mOutType

findDOutType : (dOutType : Type)
            -> (funType : (DFun  mXTypeFun mWTypeFun df dOutType))
            -> Type
findDOutType dOutType funType = dOutType

applAFun : {valueType : Type}
        -> {funType : Type}
        -> (fun : funType)
        -> (value : valueType)
        -> case valueType of
            (Monadic mXType)       => case funType of
                                       (MFun mXType f outType) => Type
                                       _ => ()
            (Dyadic dXType wXType) => case funType of
                                       (DFun mXType mWType f outType) => Type
                                       _ => ()
            _ => ()
applAFun {valueType = (Monadic mXTypeF)} {funType = (MFun mXType f outType)} fun value = ?a1
applAFun {valueType = (Dyadic dXTypeF dWTypeF)} {funType = (DFun mXType dXType f outType)} fun value = ?a2
applAFun _ _ = ?a3

-- applyType : {valueType : Type}
--           -> {funType : Type}
--           -> (value : valueType)
--           -> (fun : funType)
--           -> case valueType of
--                (Monadic mXType) => case funType of
--                                     mf@(MFun mXType f outType) => mf
--                                     _ => ()
--                (Dyadic dXType dWType) => case funType of
--                                            df@(DFun dXTypeFun dWTypeFun f outType) => df
--                                            _ => ()
--                _ => ()
-- applyType {valueType = (Monadic _)} {funType = (MFun _  _ _)} (MV mX) (MF f) = MF f
-- applyType {valueType = (Dyadic _ _)} {funType = (DFun _ _  _ _)} (DV dX dW) (DF f) = DF f
-- applyType _ _  = ?a3


-- apply : {valueType : Type}
--       -> {funType : Type}
--       -> (value : valueType)
--       -> (fun : funType)
--       -> Maybe res
-- apply value fun = case applyType value fun of
--                    (Just (MFun mXType f outType))        => ?rhs
--                    (Just (DFun dXType dWType f outType)) => ?rhs2
--                    Nothing                               => Nothing
