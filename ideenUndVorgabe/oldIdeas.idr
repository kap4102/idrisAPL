
-- retType : {outTypeM : Type} -> {outTypeD : Type}
--         -> {s : Shape} -> {sM' : Shape} -> {sD' : Shape}
--         -> (aplType : AplType inType)
--         -> (MonadicF : Maybe (Array sM inType -> Maybe (Array sM' outTypeM)))
--         -> (DyadicF  : Maybe (Array xsD inType -> Array wsD inType -> Maybe (Array sD' outTypeD)))
--         -> Type
-- retType (Monadic x) (Just y) dyadicf   =  Array sM' outTypeM
-- retType (Dyadic x w) monadicf (Just y) = Array sD' outTypeD
-- retType _ _ _ = ()

-- data AFunType :  (xType : Type) -> (wType : Type) -> (mOut : Maybe (Array mS' mOutType)) -> (dOut : Maybe (Array dS' dOutType)) -> Type where
--   AFun :  {xsM : Shape}->  {xs : Shape} -> {ws : Shape} -> (mOut : Maybe (Array mS' mOutType)) -> (dOut : Maybe (Array dS' dOutType))
--        -> (MonadicF : Maybe (Array xsM xType -> mOut))
--        -> (DyadicF  : Maybe (Array xs xType -> Array ws wType -> dOut))
--        -- -> (res : Maybe (retType aplType MonadicF DyadicF))-- perhaps Union or Either for outType
--        -> AFunType inType aplType mOutType dOutType

-- applyAF : (aFun : AFunType xType wType mOut dOut)
--         -> (aplType : AplType xType wType)
--         -> case aplType of
--                 (Monadic x)  => case mOut of
--                                  (Just _) => mOut
--                                  _        => ()
--                 (Dyadic x w) => case mOut of
--                                  (Just _) => dOut
--                                  _        => ()

-- applyAF : {s : Shape} -> {sM : Shape} -> {xsD : Shape} -> {wsD : Shape}
--         -> {sM' : Shape} -> {sD' : Shape}
--         -> (aFun : AFunType inType aplType outType)
--         -> (aplType : AplType inType)
--         -> case aplType of
--             (Monadic x)   => case aFun of
--                               (AFun (Just monadicf) _) => Maybe (Array sM' outType)
--                               _ => ()
--             (Dyadic x w)  => case aFun of
--                               (AFun (Just dyadicf) _)  => Maybe (Array sD' outType)
--                               _ => ()

Functor (Array s) where
 map f (Data ravel) = Data $ map f ravel

-- Functor (AFunType inType) where
--   map f afun = map f $ applyAF afun

Scalar : Type -> Type
Scalar v = Array [] v

-- monTally : Array s aType -> Maybe (Scalar Nat)
-- monTally x = Just $ Data $ case getShape x of
--                        [] => [1]
--                        (x::xs) => [x]

-- tally : {aTypeD} -> AFunType
-- tally = AFun (Just monTally) Nothing

-- amap : (f : aType -> aType') -> AplType aType -> Array s aType'
-- amap f (Monadic x) = map f x
-- amap f (Dyadic x w) = zipWith f x w

-- each : (f : AplType aType -> Array s aType) -> AplType aType -> Array s' a'
-- each f (Monadic x) = map f ?rhs
-- each f (Dyadic x w) = ?each_rhs_1
--
-- data AplType : (xTy : Type) -> (wTy : Type)-> Type where
--   Monadic : {xTy : Type} -> {s : Shape} -> (x : Array s xTy) -> AplType xTy wTy
--   Dyadic : {xTy : Type} -> {wTy : Type} -> {xs : Shape} -> {ws : Shape}-> (x : Array xs xTy) -> (w : Array ws wTy) -> AplType xTy wTy
