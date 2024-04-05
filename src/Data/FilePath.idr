||| A small API for working with file and directory
||| paths, with the ability to distinguish between relative
||| and absolute paths at the type level.
module Data.FilePath

import public Data.FilePath.Body
import public Data.List1
import public Data.Maybe
import public Data.String

%default total

--------------------------------------------------------------------------------
--          Path
--------------------------------------------------------------------------------

export infixl 5 </>, />

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
  PAbs   : SnocList Body -> Path Abs

  ||| A relative path
  PRel   : SnocList Body -> Path Rel

||| Concatenate two paths, the second of which must be
||| relative.
public export
(</>) : Path t -> Path Rel -> Path t
(</>) (PAbs sx) (PRel sy) = PAbs (sx ++ sy)
(</>) (PRel sx) (PRel sy) = PRel (sx ++ sy)

||| Append a file or directory to a path.
export %inline
(/>) : Path t -> Body -> Path t
fp /> s = fp </> PRel [< s]

||| Try and split a path into parent directory and
||| file/directory name.
public export
split : Path t -> Maybe (Path t, Body)
split (PAbs (sx :< x)) = Just (PAbs sx, x)
split (PRel (sx :< x)) = Just (PRel sx, x)
split (PAbs [<])       = Nothing
split (PRel [<])       = Nothing

||| Append a file ending to a path. If the path is empty,
||| this appends a hidden file/directory by prepending the
||| name with a dot.
export
(<.>) : Path t -> Body -> Path t
PAbs (sx :< x) <.> s = PAbs (sx :< (x <.> s))
PRel (sx :< x) <.> s = PRel (sx :< (x <.> s))
PRel [<]       <.> s = PRel [< preDot s]
PAbs [<]       <.> s = PAbs [< preDot s]

||| The root of the file system.
public export
root : Path Abs
root = PAbs [<]

||| Checks whether an unknown path is absolute or not.
export
isAbsolute : Path t -> Bool
isAbsolute (PAbs _) = True
isAbsolute (PRel _) = False

||| Tries to extract the basename from a path.
export %inline
basename : Path t -> Maybe Body
basename = map snd . split

||| Tries to extract the parent directory from a path.
export %inline
parentDir : Path t -> Maybe (Path t)
parentDir = map fst . split

||| Returns a list of parent directories of the given path.
export
parentDirs : Path t -> List (Path t)
parentDirs fp = case parentDir fp of
  Nothing => []
  Just p  => p :: parentDirs (assert_smaller fp p)

||| Try and split a path into base name and file extension.
export
splitFileName : Path t -> Maybe (Path t, Body)
splitFileName p = do
  (p2,b)     <- split p
  (base,ext) <- split b
  pure (p2 /> base, ext)

||| Try and split a path into the stem and extension
||| of the basename.
export
stemAndExt : Path t -> Maybe (Body, Body)
stemAndExt p = split p >>= split . snd

||| Try and extract the file stem from a path.
export
fileStem : Path t -> Maybe Body
fileStem p = map fst (stemAndExt p) <|> map snd (split p)

||| Try and extract the extension from a file.
export %inline
extension : Path t -> Maybe Body
extension = map snd . stemAndExt

normAbs : SnocList Body -> SnocList Body
normAbs [<]          = [<]
normAbs (sx :< "..") = case normAbs sx of
  [<]        => [<]
  (sx2 :< _) => sx2
normAbs (sx :< x)  = normAbs sx :< x

normRel : SnocList Body -> SnocList Body
normRel [<] = [<]
normRel (sx :< "..") = case normRel sx of
  [<]           => [< ".."]
  (sx2 :< "..") => sx2 :< ".." :< ".."
  (sx2 :< _)    => sx2
normRel (sx :< x)  = normRel sx :< x

||| Remove references to parent directories (`..`)
||| by removing the according number of parent dirs.
|||
||| In case of absolute paths, excess `..`s will be
||| silently dropped.
export
normalize : Path t -> Path t
normalize (PAbs sx) = PAbs (normAbs sx)
normalize (PRel sx) = PRel (normRel sx)

||| True if the path's basename starts with a dot
export
isHidden : Path b -> Bool
isHidden (PAbs $ _ :< x) = isHidden x
isHidden (PRel $ _ :< x) = isHidden x
isHidden _               = False

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

mapToList : (a -> b) -> SnocList a -> List b -> List b
mapToList f [<]       xs = xs
mapToList f (sx :< x) xs = mapToList f sx (f x :: xs)

export
Show (Path t) where
  showPrec p (PAbs sx) = showCon p "PAbs" $ showArg sx
  showPrec p (PRel sx) = showCon p "PRel" $ showArg sx

export
Interpolation (Path t) where
  interpolate (PAbs sx) =
    fastConcat
      . ("/" ::)
      . intersperse "/"
      $ mapToList interpolate (normAbs sx) []
  interpolate (PRel sx) =
    fastConcat
      . intersperse "/"
      $ mapToList interpolate (normRel sx) []

||| Heterogeneous equality for paths
export
heq : Path t1 -> Path t2 -> Bool
heq (PAbs sx) (PAbs sy) = sx == sy
heq (PRel sx) (PRel sy) = sx == sy
heq _         _         = False


||| Heterogeneous comparison of paths
export
hcomp : Path t1 -> Path t2 -> Ordering
hcomp (PAbs sx) (PAbs sy) = compare sx sy
hcomp (PRel sx) (PRel sy) = compare sx sy
hcomp (PAbs _)  (PRel _)  = LT
hcomp (PRel _)  (PAbs _)  = GT

public export %inline
Eq (Path t) where (==) = heq

public export
Ord (Path t) where compare = hcomp

public export
Semigroup (Path Rel) where (<+>) = (</>)

public export
Monoid (Path Rel) where neutral = PRel [<]

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
||| parsing. Only valid path bodies will be kept.
export
FromString FilePath where
  fromString s = case trim s of
    "" => FP $ PRel Lin
    st => case map trim $ split ('/' ==) st of
      "" ::: ps => FP $ PAbs $ [<] <>< mapMaybe parse ps
      p  ::: ps => FP $ PRel $ [<] <>< mapMaybe parse (p :: ps)

namespace FilePath

  ||| Append a file or directory to a path.
  public export
  (/>) : FilePath -> (b : Body) -> FilePath
  FP fp /> b = FP $ fp /> b

  ||| Append a relative path do a file path.
  public export
  (</>) : FilePath -> Path Rel -> FilePath
  FP fp </> p = FP $ fp </> p

  ||| Try and split a path into parent directory and
  ||| file/directory name.
  public export
  split : FilePath -> Maybe (FilePath, Body)
  split (FP p) = map (\(fp,s) => (FP fp, s)) $ split p

  ||| Append a file ending to a path. If the path is empty,
  ||| this appends a hidden file/directory by prepending the
  ||| name with a dot.
  public export
  (<.>) : FilePath -> (b : Body) -> FilePath
  FP fp <.> s = FP $ fp <.> s

  ||| The root of the file system.
  public export
  root : FilePath
  root = FP $ PAbs [<]

  ||| Checks whether an unknown path is absolute or not.
  export
  isAbsolute : FilePath -> Bool
  isAbsolute (FP p) = isAbsolute p

  ||| Tries to extract the basename from a path.
  export %inline
  basename : FilePath -> Maybe Body
  basename = map snd . split

  ||| Tries to extract the parent directory from a path.
  export
  parentDir : FilePath -> Maybe FilePath
  parentDir = map fst . split

  ||| Returns a list of parent directories of the given path.
  export
  parentDirs : FilePath -> List FilePath
  parentDirs (FP p) = map (\p' => FP p') $ parentDirs p

  ||| Try and split a path into base name and file extension.
  export
  splitFileName : FilePath -> Maybe (FilePath, Body)
  splitFileName (FP p) = mapFst FP <$> splitFileName p

  ||| Try and split a path into the stem and extension
  ||| of the basename.
  export %inline
  stemAndExt : FilePath -> Maybe (Body, Body)
  stemAndExt (FP p) = stemAndExt p

  ||| Try and extract the file stem from a path.
  export %inline
  fileStem : FilePath -> Maybe Body
  fileStem (FP p) = fileStem p

  ||| Try and extract the extension from a file.
  export %inline
  extension : FilePath -> Maybe Body
  extension (FP p) = extension p

  ||| True if the path's basename starts with a dot
  export %inline
  isHidden : FilePath -> Bool
  isHidden (FP p) = isHidden p

--------------------------------------------------------------------------------
--          fromString
--------------------------------------------------------------------------------

||| Witness that the given file path is an absolute path
public export
data IsAbs : FilePath -> Type where
  ItIsAbs : IsAbs (FP $ PAbs sx)

public export %inline
toAbs : (fp : FilePath) -> {auto 0 prf : IsAbs fp} -> Path Abs
toAbs (FP (PAbs sx)) = PAbs sx
toAbs (FP (PRel _)) impossible

||| Witness that the given file path is an absolute path
public export
data IsRel : FilePath -> Type where
  ItIsRel : IsRel (FP $ PRel sx)

public export %inline
toRel : (fp : FilePath) -> {auto 0 prf : IsRel fp} -> Path Rel
toRel (FP (PRel sx)) = PRel sx
toRel (FP (PAbs _)) impossible

namespace AbsPath
  ||| A quite strict function for parsing absolute paths.
  ||| This only accepts valid file bodies, so no doubling
  ||| of path separators or bodies starting with or ending
  ||| on whitespace. Sorry.
  public export
  parse : String -> Maybe (Path Abs)
  parse s = case unpack s of
    '/' :: t =>
      let ps := split ('/' ==) t
       in PAbs . (Lin <><) <$> traverse fromChars (forget ps)
    _        => Nothing

  public export
  fromString :  (s : String)
             -> {auto 0 prf : IsJust (AbsPath.parse s)}
             -> Path Abs
  fromString s = fromJust (parse s)

namespace RelPath
  ||| A quite strict function for parsing relative paths.
  ||| This only accepts valid file bodies, so no doubling
  ||| of path separators or bodies starting with or ending
  ||| on whitespace. Sorry.
  public export
  parse : String -> Maybe (Path Rel)
  parse s =
    let ps := split ('/' ==) (unpack s)
     in PRel . (Lin <><) <$> traverse fromChars (forget ps)

  public export
  fromString :  (s : String)
             -> {auto 0 prf : IsJust (RelPath.parse s)}
             -> Path Rel
  fromString s = fromJust (parse s)

--------------------------------------------------------------------------------
--          Tests
--------------------------------------------------------------------------------

-- Performance test: This typechecks *much* faster than the original
-- implementation
testRel : Path Rel
testRel =
  "abdlkjf/sdf/bb/sdfljlsjdfsdfjl/kklsdj2320398we/_jkw0r/u23__0294owe/jwjf.txt"

-- Performance test: This typechecks *much* faster than the original
-- implementation
testAbs : Path Abs
testAbs =
  "/bdlkjf/sdf/bb/sdfljlsjdfsdfjl/kklsdj2320398we/_jkw0r/u23__0294owe/jwjf.txt"
