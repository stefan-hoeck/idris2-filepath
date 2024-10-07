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

public export
record DriveLetter where
  constructor MkDriveLetter
  letter : Char
  0 prf  : isAlpha letter === True

export
fromChar : (c : Char) -> {auto 0 prf : isAlpha c === True} -> DriveLetter
fromChar c = MkDriveLetter c prf

namespace DriveLetter
  public export
  parse : Char -> Maybe DriveLetter
  parse c with (isAlpha c) proof prf
    parse c | True  = Just $ MkDriveLetter c prf
    parse c | False = Nothing

export
Show DriveLetter where
  showPrec p (MkDriveLetter c _) = showCon p "MkDriveLetter" $ showArg c ++ " _"

export
Interpolation DriveLetter where
  interpolate (MkDriveLetter c _) = singleton c

export
Eq DriveLetter where
  MkDriveLetter c _ == MkDriveLetter d _ = c == d

public export
data AbsType = Unix | Disk DriveLetter | UNC Body Body

export
Show AbsType where
  showPrec p Unix        = "Unix"
  showPrec p (Disk d)    = showCon p "Disk" $ showArg d
  showPrec p (UNC sv sh) = showCon p "UNC" $ showArg sv ++ showArg sh

export
Interpolation AbsType where
  interpolate Unix        = "/"
  interpolate (Disk d)    = "\{d}:\\"
  interpolate (UNC sv sh) = "\\\\\{sv}\\\{sh}\\"

export
Eq AbsType where
  Unix == Unix = True
  Disk d == Disk d' = d == d'
  UNC sv sh == UNC sv' sh' = sv == sv' && sh == sh'
  _ == _ = False

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
  PAbs   : AbsType -> SnocList Body -> Path Abs

  ||| A relative path
  PRel   : SnocList Body -> Path Rel

||| Concatenate two paths, the second of which must be
||| relative.
public export
(</>) : Path t -> Path Rel -> Path t
(</>) (PAbs at sx) (PRel sy) = PAbs at (sx ++ sy)
(</>) (PRel sx) (PRel sy)    = PRel (sx ++ sy)

||| Append a file or directory to a path.
export %inline
(/>) : Path t -> Body -> Path t
fp /> s = fp </> PRel [< s]

||| Try and split a path into parent directory and
||| file/directory name.
public export
split : Path t -> Maybe (Path t, Body)
split (PAbs at (sx :< x)) = Just (PAbs at sx, x)
split (PRel (sx :< x))    = Just (PRel sx, x)
split (PAbs _ [<])        = Nothing
split (PRel [<])          = Nothing

||| Append a file ending to a path. If the path is empty,
||| this appends a hidden file/directory by prepending the
||| name with a dot.
export
(<.>) : Path t -> Body -> Path t
PAbs at (sx :< x) <.> s = PAbs at (sx :< (x <.> s))
PRel (sx :< x)    <.> s = PRel (sx :< (x <.> s))
PRel [<]          <.> s = PRel [< preDot s]
PAbs at [<]       <.> s = PAbs at [< preDot s]

||| The root of the file system. (unix)
public export
root : Path Abs
root = PAbs Unix [<]

||| The root of the given disk. (windows)
public export
disk : DriveLetter -> Path Abs
disk d = PAbs (Disk d) [<]

||| The root of the given network share. (windows)
public export
network : Body -> Body -> Path Abs
network sv sh = PAbs (UNC sv sh) [<]

||| Checks whether an unknown path is absolute or not.
export
isAbsolute : Path t -> Bool
isAbsolute (PAbs _ _) = True
isAbsolute (PRel _)   = False

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
normalize (PAbs at sx) = PAbs at (normAbs sx)
normalize (PRel sx)    = PRel (normRel sx)

||| True if the path's basename starts with a dot
export
isHidden : Path b -> Bool
isHidden (PAbs _ $ _ :< x) = isHidden x
isHidden (PRel $ _ :< x)   = isHidden x
isHidden _                 = False

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

mapToList : (a -> b) -> SnocList a -> List b -> List b
mapToList f [<]       xs = xs
mapToList f (sx :< x) xs = mapToList f sx (f x :: xs)

export
Show (Path t) where
  showPrec p (PAbs at sx) = showCon p "PAbs" $ showArg at ++ showArg sx
  showPrec p (PRel sx)    = showCon p "PRel" $ showArg sx

export
Interpolation (Path t) where
  interpolate (PAbs at sx) =
    concat
      . (interpolate at ::)
      . intersperse (singleton Sep)
      $ mapToList interpolate (normAbs sx) []
  interpolate (PRel [<]) = "."
  interpolate (PRel sx) =
    concat
      . intersperse (singleton Sep)
      $ mapToList interpolate (normRel sx) []

||| Heterogeneous equality for paths
export
heq : Path t1 -> Path t2 -> Bool
heq (PAbs at sx) (PAbs at' sy) = at == at' && sx == sy
heq (PRel sx) (PRel sy)        = sx == sy
heq _         _                = False


||| Heterogeneous comparison of paths
export
hcomp : Path t1 -> Path t2 -> Ordering
hcomp (PAbs at sx) (PAbs at' sy) = compare sx sy
hcomp (PRel sx) (PRel sy)        = compare sx sy
hcomp (PAbs _ _)  (PRel _)       = LT
hcomp (PRel _)  (PAbs _ _)       = GT

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
    ""  => FP $ PRel Lin
    "." => FP $ PRel Lin
    st  => case map trim $ split (\c => c == '/' || c == '\\') st of
      "" ::: "" :: sv :: sh :: ps => case (parse sv, parse sh) of
        (Just sv', Just sh') => FP $ PAbs (UNC sv' sh') $ [<] <>< mapMaybe parse ps
        _                    => FP $ PAbs Unix $ [<] <>< mapMaybe parse (sv :: sh :: ps)
      p  ::: ps                   => case strM p of
        StrNil        => FP $ PAbs Unix $ [<] <>< mapMaybe parse ps
        StrCons c ":" => case parse c of
          Just d  => FP $ PAbs (Disk d) $ [<] <>< mapMaybe parse ps
          Nothing => FP $ PRel $ [<] <>< mapMaybe parse (p :: ps)
        _         => FP $ PRel $ [<] <>< mapMaybe parse (p :: ps)

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
  root = FP $ PAbs Unix [<]

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
  ItIsAbs : IsAbs (FP $ PAbs at sx)

public export %inline
toAbs : (fp : FilePath) -> {auto 0 prf : IsAbs fp} -> Path Abs
toAbs (FP (PAbs at sx)) = PAbs at sx
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
  parse s =
    let cs := unpack s
     in parseUNC cs <|> parseDisk cs <|> parseUnix cs
    where
      parseBody : List Char -> Maybe (SnocList Body)
      parseBody t =
        let ps := split (\c => c == '/' || c == '\\') t
         in (Lin <><) <$> traverse fromChars (forget ps)

      parseUNCBody : List Char -> Maybe (Path Abs)
      parseUNCBody t = case split (\c => c == '/' || c == '\\') t of
        [] ::: _        => Nothing
        _ ::: [] :: _   => Nothing
        sv ::: sh :: ps => Just $ PAbs (UNC !(fromChars sv) !(fromChars sh)) ((Lin <><) !(traverse fromChars ps))
        _               => Nothing

      parseUnix : List Char -> Maybe (Path Abs)
      parseUnix ('/' :: t)  = PAbs Unix <$> parseBody t
      parseUnix ('\\' :: t) = PAbs Unix <$> parseBody t
      parseUnix _           = Nothing

      parseDisk : List Char -> Maybe (Path Abs)
      parseDisk (d :: ':' :: '/' :: t)  = [| PAbs (Disk <$> parse d) (parseBody t) |]
      parseDisk (d :: ':' :: '\\' :: t) = [| PAbs (Disk <$> parse d) (parseBody t) |]
      parseDisk _                       = Nothing

      parseUNC : List Char -> Maybe (Path Abs)
      parseUNC ('/' :: '/' :: t)   = parseUNCBody t
      parseUNC ('\\' :: '\\' :: t) = parseUNCBody t
      parseUNC _                   = Nothing

  public export
  fromString :
       (s : String)
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
  parse "." = Just (PRel [<])
  parse s =
    let ps := split (\c => c == '/' || c == '\\') (unpack s)
     in PRel . (Lin <><) <$> traverse fromChars (forget ps)

  public export
  fromString :
       (s : String)
    -> {auto 0 prf : IsJust (RelPath.parse s)}
    -> Path Rel
  fromString s = fromJust (parse s)

||| A quite strict function for parsing absolute paths.
||| This only accepts valid file bodies, so no doubling
||| of path separators or bodies starting with or ending
||| on whitespace. Sorry.
public export
parse : String -> Maybe FilePath
parse str = FP <$> AbsPath.parse str
        <|> FP <$> RelPath.parse str

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
testAbsUnix : Path Abs
testAbsUnix =
  "/bdlkjf/sdf/bb/sdfljlsjdfsdfjl/kklsdj2320398we/_jkw0r/u23__0294owe/jwjf.txt"

-- Performance test: This typechecks *much* faster than the original
-- implementation
testAbsDisk : Path Abs
testAbsDisk =
  "C:\\bdlkjf\\sdf\\bb\\sdfljlsjdfsdfjl\\kklsdj2320398we\\_jkw0r\\u23__0294owe\\jwjf.txt"

-- Performance test: This typechecks *much* faster than the original
-- implementation
testAbsUNC : Path Abs
testAbsUNC =
  "\\\\localhost\\share\\dfljlsjdfsdfjl\\kklsdj2320398we\\_jkw0r\\u23__0294owe\\jwjf.txt"
