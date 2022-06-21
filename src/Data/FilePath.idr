module Data.FilePath

import Data.DPair
import Data.List1
import Data.String

%default total

public export
Sep : String
Sep = "/"

public export
dropEnd : Nat -> SnocList a -> (Nat, SnocList a)
dropEnd 0     sx        = (0, sx)
dropEnd k     [<]       = (k, [<])
dropEnd (S k) (sx :< x) = dropEnd k sx

||| Proof that the given string does not contain the path separator
public export
0 NoSep : String -> Type
NoSep s = isInfixOf Sep s === False

||| Checks if the given string does not contain a
||| path separator.
public export
noSep : String -> Maybe (Subset String NoSep)
noSep s with (isInfixOf Sep s) proof prf
  _ | False = Just (Element s prf)
  _ | True  = Nothing

||| True, if the given path body corresponds to the
||| current directory symbol (`.`).
public export
isCurrent : String -> Bool
isCurrent "." = True
isCurrent _   = False

||| True, if the given path body corresponds to the
||| parent directory symbol (`..`).
public export
isParent : String -> Bool
isParent ".." = True
isParent _    = False

||| True, if the given path body does not correspond to the
||| current or parent directory symbol.
public export
notSpecial : String -> Bool
notSpecial s = not (isCurrent s || isParent s)

--------------------------------------------------------------------------------
--          Path
--------------------------------------------------------------------------------

infixl 5 </>, />
infixr 7 <.>

||| A path in the file system is either relative
||| or absolute.
public export
data PathType = Rel | Abs

||| A path in the file system.
|||
||| Right now, only Unix-style paths are supported.
public export
data Path : PathType -> Type where
  ||| An absolute path
  PAbs   : SnocList String -> Path Abs

  ||| A relative path, prefixed with the given number of
  ||| parent directory tokens (`..`).
  PRel   : (nrParents : Nat) -> SnocList String -> Path Rel

||| Concatenate two paths, the second of which must be
||| relative.
|||
||| If the second path has `n` parent directory tokens,
||| at most `n` levels will be removed from the end of
||| the first paths list of bodies. Excess numbers of parent
||| directories will be silently dropped in case of absolute
||| paths. In case of relative paths, they will be added to
||| the number of parent tockens of the left path.
public export
(</>) : Path t -> Path Rel -> Path t
(</>) (PAbs sx)   (PRel n sy) = PAbs (snd (dropEnd n sx) ++ sy)
(</>) (PRel m sx) (PRel n sy) =
  let (n',sx') = dropEnd n sx in PRel (m + n') (sx' ++ sy)

||| Append a file or directory to a path.
export
(/>) : Path t -> (s : String) -> {auto 0 prf : NoSep s} -> Path t
fp /> s = case trim s of
  ""   => fp
  "."  => fp
  ".." => fp </> PRel 1 [<]
  st   => fp </> PRel 0 [< st]

||| Try and split a path into parent directory and
||| file/directory name.
public export
split : Path t -> Maybe (Path t, String)
split (PAbs (sx :< x))   = Just (PAbs sx, x)
split (PRel n (sx :< x)) = Just (PRel n sx, x)
split (PAbs [<])         = Nothing
split (PRel _ [<])       = Nothing

||| Append a file ending to a path. If the path is empty,
||| this appends a hidden file/directory by prepending the
||| name with a dot.
export
(<.>) : Path t -> (s : String) -> {auto 0 prf : NoSep s} -> Path t
PAbs (sx :< x)   <.> s = PAbs (sx :< "\{x}.\{s}")
PRel n (sx :< x) <.> s = PRel n (sx :< "\{x}.\{s}")
PRel n [<]       <.> s = PRel n [< ".\{s}"]
PAbs [<]         <.> s = PAbs [< ".\{s}"]

||| The root of the file system.
public export
root : Path Abs
root = PAbs [<]

||| Checks whether an unknown path is absolute or not.
export
isAbsolute : Path t -> Bool
isAbsolute (PAbs _)   = True
isAbsolute (PRel _ _) = False

||| Tries to extract the parent directory from a path.
export
parentDir : Path t -> Maybe (Path t)
parentDir = map fst . split

||| Returns a list of parent directories of the given path.
export
parentDirs : Path t -> List (Path t)
parentDirs fp = case parentDir fp of
  Nothing => []
  Just p  => p :: parentDirs (assert_smaller fp p)

namespace Subset
  ||| Append a file or directory to a path.
  export %inline
  (/>) : Path t -> Subset String NoSep -> Path t
  fp /> Element s _ = fp /> s

  ||| Append a file ending to a path. If the path is empty,
  ||| this appends a hidden file/directory by prepending the
  ||| name with a dot.
  export %inline
  (<.>) : Path t -> Subset String NoSep -> Path t
  fp <.> Element s _ = fp <.> s

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

export
Show (Path t) where
  show (PAbs sx)   =
    fastConcat . ("/" ::) . intersperse "/" $ sx <>> []
  show (PRel n sx) =
    fastConcat . intersperse "/" $ replicate n ".." ++ (sx <>> [])

export
Interpolation (Path t) where
  interpolate = show

export
heq : Path t1 -> Path t2 -> Bool
heq (PAbs sx)   (PAbs sy)   = sx == sy
heq (PRel m sx) (PRel n sy) = m == n && sx == sy
heq _           _           = False

export
hcomp : Path t1 -> Path t2 -> Ordering
hcomp (PAbs sx)   (PAbs sy)   = compare sx sy
hcomp (PRel m sx) (PRel n sy) = case compare m n of
  EQ => compare sx sy
  o  => o
hcomp (PAbs _)    (PRel _ _)  = LT
hcomp (PRel _ _)  (PAbs _)    = GT

public export %inline
Eq (Path t) where (==) = heq

public export
Ord (Path t) where compare = hcomp

public export
Semigroup (Path Rel) where (<+>) = (</>)

public export
Monoid (Path Rel) where neutral = PRel 0 [<]

--------------------------------------------------------------------------------
--          FilePath
--------------------------------------------------------------------------------

||| A path (relative or absolute) in a file system.
public export
record FilePath where
  constructor FP
  {0 pathType : PathType}
  path        : Path pathType

public export %inline
Eq FilePath where
  FP p1 == FP p2 = heq p1 p2

public export
Ord FilePath where
  compare (FP p1) (FP p2) = hcomp p1 p2

export
Show FilePath where show (FP p) = show p

export
Interpolation FilePath where interpolate (FP p) = interpolate p

||| Tries to parse a file path as faithfully as possible.
|||
||| All whitespace on the left and right is trimmed before
||| parsing. All current directory and parent directory symbols
||| (`.` and `..`) in the middle of the path will be dropped.
public export
FromString FilePath where
  fromString s = case trim s of
    "" => FP $ PRel 0 Lin
    st => case split ('/' ==) st of
      ""  ::: ps => FP $ PAbs $ [<] <>< filter notSpecial ps
      "." ::: ps => FP $ PRel 0 $ [<] <>< filter notSpecial ps
      p   ::: ps =>
        let (pre,post) = break (not . isParent) (p :: ps)
         in FP $ PRel (length pre) $ [<] <>< filter notSpecial post

namespace FilePath

  ||| Append a file or directory to a path.
  public export
  (/>) : FilePath -> (s : String) -> {auto 0 prf : NoSep s} -> FilePath
  FP fp /> s = FP $ fp /> s

  ||| Append a relative path do a file path.
  public export
  (</>) : FilePath -> Path Rel -> FilePath
  FP fp </> p = FP $ fp </> p

  ||| Try and split a path into parent directory and
  ||| file/directory name.
  public export
  split : FilePath -> Maybe (FilePath, String)
  split (FP p) = map (\(fp,s) => (FP fp, s)) $ split p

  ||| Append a file ending to a path. If the path is empty,
  ||| this appends a hidden file/directory by prepending the
  ||| name with a dot.
  public export
  (<.>) : FilePath -> (s : String) -> {auto 0 prf : NoSep s} -> FilePath
  FP fp <.> s = FP $ fp <.> s

  ||| The root of the file system.
  public export
  root : FilePath
  root = FP $ PAbs [<]

  ||| Checks whether an unknown path is absolute or not.
  export
  isAbsolute : FilePath -> Bool
  isAbsolute (FP p) = isAbsolute p

  ||| Tries to extract the parent directory from a path.
  export
  parentDir : FilePath -> Maybe FilePath
  parentDir = map fst . split

  ||| Returns a list of parent directories of the given path.
  export
  parentDirs : FilePath -> List FilePath
  parentDirs (FP p) = map (\p' => FP p') $ parentDirs p

  namespace Subset
    ||| Append a file or directory to a path.
    export %inline
    (/>) : FilePath -> Subset String NoSep -> FilePath
    fp /> Element s _ = fp /> s

    ||| Append a file ending to a path. If the path is empty,
    ||| this appends a hidden file/directory by prepending the
    ||| name with a dot.
    export %inline
    (<.>) : FilePath -> Subset String NoSep -> FilePath
    fp <.> Element s _ = fp <.> s
