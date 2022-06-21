||| This provides a more or less reasonable representation for
||| bodies in a file path.
module Data.FilePath.Body

%default total

--------------------------------------------------------------------------------
--          Dec0
--------------------------------------------------------------------------------

||| Decidability with erased proofs
public export
data Dec0 : t -> Type where
  Yes0 : (0 prf : t) -> Dec0 t
  No0  : (0 contra : t -> Void) -> Dec0 t

public export
data IsYes : Dec0 t -> Type where
  ItIsYes : IsYes (Yes0 prf)

public export
0 fromYes : (d : Dec0 t) -> {auto _ : IsYes d} -> t
fromYes (Yes0 prf) = prf

--------------------------------------------------------------------------------
--          Constants
--------------------------------------------------------------------------------

public export %inline
Sep : Char
Sep = '/'

--------------------------------------------------------------------------------
--          BodyChar
--------------------------------------------------------------------------------

||| A character acceptable in the middle of a path body.
||| We don't allow path separators and control characters in path bodies.
public export
isBodyChar : Char -> Bool
isBodyChar '/' = False
isBodyChar c   = not (isControl c)

public export
data BodyChar : Char -> Type where
  IsBodyChar : (0 prf : isBodyChar c === True) -> BodyChar c

public export
bodyChar : (c : Char) -> Dec0 (BodyChar c)
bodyChar c with (isBodyChar c) proof eq
  _ | True  = Yes0 (IsBodyChar eq)
  _ | False = No0 $ \(IsBodyChar prf) => absurd (trans (sym prf) eq)


export
Uninhabited (BodyChar '\t') where
  uninhabited (IsBodyChar prf) impossible

export
Uninhabited (BodyChar '\r') where
  uninhabited (IsBodyChar prf) impossible

export
Uninhabited (BodyChar '\n') where
  uninhabited (IsBodyChar prf) impossible

export
Uninhabited (BodyChar '\b') where
  uninhabited (IsBodyChar prf) impossible

export
Uninhabited (BodyChar '\0') where
  uninhabited (IsBodyChar prf) impossible

--------------------------------------------------------------------------------
--          EndChar
--------------------------------------------------------------------------------

||| Character at the end of a path body.
||| Although theoretically allowed in Unix paths, we don't
||| allow trailing spaces for reasons of sanity.
public export
data EndChar : Char -> Type where
  IsEndChar : (0 ib : BodyChar c) -> (0 prf : (c == ' ') === False) -> EndChar c

export
Uninhabited (EndChar ' ') where
  uninhabited (IsEndChar _ prf) impossible

public export
0 endCharImpliesBodyChar : EndChar c -> BodyChar c
endCharImpliesBodyChar (IsEndChar ib _) = ib

public export
endChar : (c : Char) -> Dec0 (EndChar c)
endChar c with (c == ' ') proof eq
  _ | True  = No0 $ \(IsEndChar _ prf) => absurd (trans (sym prf) eq)
  _ | False = case bodyChar c of
    Yes0 ib    => Yes0 (IsEndChar ib eq)
    No0 contra => No0 $ \ec => contra (endCharImpliesBodyChar ec)

--------------------------------------------------------------------------------
--          SingleChar
--------------------------------------------------------------------------------

||| We don't accept path bodies consisting of a single dot.
public export
data SingleChar : Char -> Type where
  IsSingleChar : (0 ie : EndChar c) -> (0 prf : (c == '.') === False) -> SingleChar c

export
Uninhabited (SingleChar '.') where
  uninhabited (IsSingleChar _ prf) impossible

public export
0 singleCharImpliesEndChar : SingleChar c -> EndChar c
singleCharImpliesEndChar (IsSingleChar ie _) = ie

public export
singleChar : (c : Char) -> Dec0 (SingleChar c)
singleChar c with (c == '.') proof eq
  _ | True  = No0 $ \(IsSingleChar _ prf) => absurd (trans (sym prf) eq)
  _ | False = case endChar c of
    Yes0 ie    => Yes0 (IsSingleChar ie eq)
    No0 contra => No0 $ \sc => contra (singleCharImpliesEndChar sc)

public export
data BodyInner : List Char -> Type where
  End  : (0 prf : EndChar c) -> BodyInner [c]
  Cons : (0 prf : BodyChar c) -> (0 bi : BodyInner cs) -> BodyInner (c :: cs)

public export
data BodyChars : List Char -> Type where
  One  : (0 prf : SingleChar c) -> BodyChars [c]
  Many : (0 prf : EndChar c) -> (0 bi : BodyInner cs) -> BodyChars (c :: cs)

export
Uninhabited (BodyChars []) where
  uninhabited One impossible
  uninhabited (Many _ _) impossible

export
Uninhabited (BodyChars ['.']) where
  uninhabited (One prf) = void $ absurd prf
  uninhabited (Many _ _) impossible

--------------------------------------------------------------------------------
--          Concatenation Proofs
--------------------------------------------------------------------------------

export
0 toInner : BodyChars xs -> BodyInner xs
toInner (One prf)     = End (singleCharImpliesEndChar prf)
toInner (Many prf bi) = Cons (endCharImpliesBodyChar prf) bi

export
0 appendInnerChars : BodyInner xs -> BodyInner ys -> BodyInner (xs ++ ys)
appendInnerChars (End p)     y = Cons (endCharImpliesBodyChar p) y
appendInnerChars (Cons p bi) y = Cons p $ appendInnerChars bi y

export
0 appendBodyChars : BodyChars xs -> BodyChars ys -> BodyChars (xs ++ ys)
appendBodyChars (One p)     y = Many (singleCharImpliesEndChar p) (toInner y)
appendBodyChars (Many p bi) y = Many p (appendInnerChars bi $ toInner y)

export
0 preDotBodyChars : BodyChars cs -> BodyChars ('.' :: cs)
preDotBodyChars (One p) = Many %search (End $ singleCharImpliesEndChar p)
preDotBodyChars (Many p bi) = Many %search (Cons (endCharImpliesBodyChar p) bi)

--------------------------------------------------------------------------------
--          Body
--------------------------------------------------------------------------------

||| A single body in a path. This is represented as a list of characters,
||| since otherwise we'd have to constantly unpack and pack this anyway.
public export
record Body where
  constructor MkBody
  body  : List Char
  0 prf : BodyChars body

public export %inline
Eq Body where
  MkBody x _ == MkBody y _ = x == y

public export %inline
Ord Body where
  compare (MkBody x _) (MkBody y _) = compare x y

export
Show Body where
  showPrec p (MkBody b _) = showCon p "MkBody" $ showArg b ++ " _"

public export %inline
Interpolation Body where
  interpolate (MkBody b _) = pack b

export %inline
Semigroup Body where
  MkBody x px <+> MkBody y py = MkBody (x ++ y) (appendBodyChars px py)

public export
innerChars : (c : Char) -> (cs : List Char) -> Dec0 (BodyInner $ c :: cs)
innerChars c [] = case endChar c of
  Yes0 ec    => Yes0 (End ec)
  No0 contra => No0 $ \(End ec) => contra ec
innerChars c (h :: t) = case bodyChar c of
  No0 contra => No0 $ \(Cons prf bi) => contra prf
  Yes0 prf   => case innerChars h t of
    Yes0 bi => Yes0 (Cons prf bi)
    No0 contra => No0 $ \(Cons prf bi) => contra bi

public export
bodyChars : (cs : List Char) -> Dec0 (BodyChars cs)
bodyChars [] = No0 $ \prf => absurd prf
bodyChars (x :: [])     = case singleChar x of
  Yes0 prf   => Yes0 (One prf)
  No0 contra => No0 $ \(One prf) => contra prf
bodyChars (c :: h :: t) = case endChar c of
  Yes0 ec => case innerChars h t of
    Yes0 bi => Yes0 (Many ec bi)
    No0 contra => No0 $ \(Many _ bi) => contra bi
  No0 contra => No0 $ \(Many ec _) => contra ec

public export
fromString : (s : String) -> {auto 0 p : IsYes (bodyChars $ unpack s)} -> Body
fromString s = MkBody (unpack s) (fromYes $ bodyChars (unpack s))

export
preDot : Body -> Body
preDot (MkBody cs p) = MkBody ('.' :: cs) (preDotBodyChars p)
