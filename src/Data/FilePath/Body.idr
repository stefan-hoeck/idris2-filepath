||| This provides a more or less reasonable representation for
||| bodies in a file path.
module Data.FilePath.Body

import Data.List
import Data.List1
import System.Info

%default total

--------------------------------------------------------------------------------
--          Utils
--------------------------------------------------------------------------------

public export
check : (b : Bool) -> Maybe (b === True)
check False = Nothing
check True  = Just Refl

0 unAnd : {x,y : Bool} -> (x && y) === True -> (x === True, y === True)
unAnd {x = True}  {y = True}  _ = (Refl,Refl)
unAnd {x = True}  {y = False} _ impossible
unAnd {x = False} {y = _}     _ impossible

0 unAnd1 : {x,y : Bool} -> (x && y) === True -> x === True
unAnd1 = fst . unAnd

0 unAnd2 : {x,y : Bool} -> (x && y) === True -> y === True
unAnd2 = snd . unAnd

0 and : {x,y : Bool} -> x === True -> y === True -> (x && y) === True
and {x = True}  {y = True}  _ _ = Refl
and {x = True}  {y = False} _ _ impossible
and {x = False} {y = _}     _ _ impossible

--------------------------------------------------------------------------------
--          Constants
--------------------------------------------------------------------------------

||| The platform dependent path separator
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
isBodyChar '/'  = False
isBodyChar '\\' = False
isBodyChar c    = not (isControl c)

public export
0 BodyChar : Char -> Type
BodyChar c = isBodyChar c === True

export
0 notBodyCharTab : BodyChar '\t' -> Void
notBodyCharTab prf impossible

export
0 notBodyCharRet : BodyChar '\r' -> Void
notBodyCharRet prf impossible

export
0 notBodyCharNL : BodyChar '\n' -> Void
notBodyCharNL prf impossible

export
0 notBodyCharB : BodyChar '\b' -> Void
notBodyCharB prf impossible

export
0 notBodyChar0 : BodyChar '\0' -> Void
notBodyChar0 prf impossible

--------------------------------------------------------------------------------
--          EndChar
--------------------------------------------------------------------------------

||| We don't accept spaces at the end of path bodies.
public export
isEndChar : Char -> Bool
isEndChar c = isBodyChar c && c /= ' '

public export
0 EndChar : Char -> Type
EndChar c = isEndChar c === True

export
Uninhabited (EndChar ' ') where
  uninhabited prf impossible

export
0 notEndCharSpace : EndChar ' ' -> Void
notEndCharSpace prf impossible

--------------------------------------------------------------------------------
--          SingleChar
--------------------------------------------------------------------------------

||| We don't accept path bodies consisting of a single dot.
public export
isSingleChar : Char -> Bool
isSingleChar c = isEndChar c && c /= '.'

public export
0 SingleChar : Char -> Type
SingleChar c = isSingleChar c === True

export
0 notSingleCharDot : SingleChar '.' -> Void
notSingleCharDot prf impossible

--------------------------------------------------------------------------------
--          BodyInner
--------------------------------------------------------------------------------

||| True if the given list of characters can appear after the initial
||| character of a path body.
public export
isBodyInner : List Char -> Bool
isBodyInner []        = False
isBodyInner (x :: []) = isEndChar x
isBodyInner (x :: xs) = isBodyChar x && isBodyInner xs

public export
0 BodyInner : List Char -> Type
BodyInner xs = isBodyInner xs === True

||| True if the given list of characters represent a valid path body.
public export
isBodyChars : List Char -> Bool
isBodyChars []        = False
isBodyChars (x :: []) = isSingleChar x
isBodyChars (x :: xs) = isEndChar x && isBodyInner xs

public export
0 BodyChars : List Char -> Type
BodyChars xs = isBodyChars xs === True

0 notBodyCharsEmpty : BodyChars [] -> Void
notBodyCharsEmpty refl impossible

0 notBodyCharsDot : BodyChars ['.'] -> Void
notBodyCharsDot refl impossible

--------------------------------------------------------------------------------
--          Concatenation Proofs
--------------------------------------------------------------------------------

export
0 toInner : (xs : List Char) -> BodyChars xs -> BodyInner xs
toInner (x :: [])      prf = unAnd1 prf
toInner (x :: y :: ys) prf =
  let (p1,p2) = unAnd prf in and (unAnd1 p1) p2
toInner []             prf impossible

export
0 appendInnerChars :
     (xs,ys : List Char)
  -> BodyInner xs
  -> BodyInner ys
  -> BodyInner (xs ++ ys)
appendInnerChars (h :: [])      (y :: ys) prf1 prf2 =
  and (unAnd1 prf1) prf2
appendInnerChars (h :: t@(x :: xs)) ys prf1 prf2 =
  and (unAnd1 prf1) (appendInnerChars t ys (unAnd2 prf1) prf2)
appendInnerChars [] _ _ _ impossible
appendInnerChars _  [] _ _ impossible

export
0 appendBodyChars :
     (xs,ys : List Char)
  -> BodyChars xs
  -> BodyChars ys
  -> BodyChars (xs ++ ys)
appendBodyChars (h :: [])      (y :: ys) prf1 prf2 =
  and (unAnd1 prf1) (toInner (y :: ys) prf2)
appendBodyChars (h :: x :: xs) ys prf1 prf2 =
  and (unAnd1 prf1) (appendInnerChars _ _ (unAnd2 prf1) $ toInner _ prf2)
appendBodyChars [] _ _ _ impossible
appendBodyChars _  [] _ _ impossible

export
0 preDotBodyChars : (cs : List Char) -> BodyChars cs -> BodyChars ('.' :: cs)
preDotBodyChars (h :: t) prf = toInner _ prf
preDotBodyChars [] prf impossible

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
  MkBody x px <+> MkBody y py = MkBody (x ++ y) (appendBodyChars _ _px py)


||| Tries to convert a list of character to a body
public export
fromChars : List Char -> Maybe Body
fromChars cs = case check (isBodyChars cs) of
  Just prf => Just $ MkBody cs prf
  Nothing  => Nothing

||| Tries to convert a string to a body
public export %inline
parse : String -> Maybe Body
parse = fromChars . unpack

public export
fromString : (s : String) -> {auto 0 p : BodyChars (unpack s)} -> Body
fromString s = MkBody (unpack s) p

export
preDot : Body -> Body
preDot (MkBody cs p) = MkBody ('.' :: cs) (preDotBodyChars _ p)

export infixr 7 <.>

||| Append a file ending to a path body.
export
(<.>) : Body -> Body -> Body
x <.> y = x <+> preDot y

||| Tries to split a path body into its stem an extension.
export
split : Body -> Maybe (Body,Body)
split (MkBody b _) =
  let ss := split ('.' ==) b
   in [| MkPair
           (fromChars $ join $ intersperse ['.'] (init ss))
           (fromChars $ last ss) |]

||| Tries to extract a stem from a file name.
export %inline
fileStem : Body -> Maybe Body
fileStem = map fst . split

||| True if the file body starts with a dot.
export
isHidden : Body -> Bool
isHidden (MkBody ('.' :: _) _) = True
isHidden _                     = False

||| Tries to extract an extension from a file name.
export %inline
extension : Body -> Maybe Body
extension = map snd . split

--------------------------------------------------------------------------------
--          Tests
--------------------------------------------------------------------------------

-- Performance test: This typechecks *much* faster than the original
-- implementation
test : Body
test =
  fromString $
       "sdfljlsjdfsdfjl_kklsdfkj2320398wejjkwe0r9u23__02394oweijwjf"
    ++ "sdfljlsjdfsdfjl_kklsdfkj2320398wejjkwe0r9u23__02394oweijwjf"
    ++ "sdfljlsjdfsdfjl_kklsdfkj2320398wejjkwe0r9u23__02394oweijwjf"
    ++ "sdfljlsjdfsdfjl_kklsdfkj2320398wejjkwe0r9u23__02394oweijwjf"
