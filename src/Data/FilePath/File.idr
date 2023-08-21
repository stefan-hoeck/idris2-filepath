||| Relative and absolute file paths, which are guaranteed
||| to consist of a basename plus parent directory.
module Data.FilePath.File

import public Data.FilePath

%default total

||| A file path consists of a basename and a parent
||| directory, which is either a relative or absolute
||| path.
public export
record File (t : PathType) where
  constructor MkF
  parent : Path t
  file   : Body

public export %inline
toPath : File t -> Path t
toPath (MkF p b) = p /> b

||| Concatenate a path with a relative file path.
public export %inline
(</>) : Path t -> File Rel -> File t
(</>) p (MkF p2 f) = MkF (p </> p2) f

||| Append a file or directory to a path.
export %inline
(/>) : Path t -> Body -> File t
(/>) = MkF

||| Split a file path into its parent directory and
||| base name.
public export %inline
split : File t -> (Path t, Body)
split (MkF p b) = (p,b)

||| Append a file ending to a path. If the path is empty,
||| this appends a hidden file/directory by prepending the
||| name with a dot.
export %inline
(<.>) : File t -> Body -> File t
(<.>) (MkF p f) ext = MkF p (f <.> ext)

||| Checks whether an unknown path is absolute or not.
export %inline
isAbsolute : File t -> Bool
isAbsolute = isAbsolute . parent

||| True if the file's basename starts with a dot.
export %inline
isHidden : File t -> Bool
isHidden (MkF p f) = isHidden f

||| Extract the basename from a file path.
export %inline
basename : File t -> Body
basename = file

||| Returns a list of parent directories of the given path.
export %inline
parentDirs : File t -> List (Path t)
parentDirs (MkF p f) = FilePath.parentDirs $ p /> f

||| Try and split a path into the stem and extension
||| of the basename.
export
splitFileName : File t -> Maybe (File t, Body)
splitFileName (MkF p f) = do
  (b,ext) <- split f
  pure $ (MkF p b, ext)

||| Try and split a path into the stem and extension
||| of the basename.
export
stemAndExt : File t -> Maybe (Body, Body)
stemAndExt = map (\(MkF _ s, ext) => (s,ext)) . splitFileName

||| Try and extract the file stem from a file path.
export %inline
fileStem : File t -> Maybe Body
fileStem = map fst . stemAndExt

||| Try and extract the extension from a file.
export %inline
extension : File t -> Maybe Body
extension = map snd . stemAndExt

||| Remove references to parent directories (`..`)
||| by removing the according number of parent dirs.
|||
||| In case of absolute paths, excess `..`s will be
||| silently dropped.
export %inline
normalize : File t -> File t
normalize (MkF p b) = MkF (normalize p) b

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

export
Show (File t) where
  showPrec p (MkF q b) = showCon p "MkF" $ showArg q ++ showArg b

export %inline
Interpolation (File t) where
  interpolate = interpolate . toPath

public export
Eq (File t) where
  f == g = toPath f == toPath g

public export %inline
Ord (File t) where
  compare f g = compare (toPath f) (toPath g)

--------------------------------------------------------------------------------
--          fromString
--------------------------------------------------------------------------------

namespace AbsFile
  ||| A quite strict function for parsing absolute file paths.
  ||| This only accepts valid file bodies, so no doubling
  ||| of path separators or bodies starting with or ending
  ||| on whitespace. Sorry.
  public export
  parse : String -> Maybe (File Abs)
  parse s = case AbsPath.parse s of
    Just (PAbs $ sx :< x) => Just $ MkF (PAbs sx) x
    _                     => Nothing

  public export
  fromString :
       (s : String)
    -> {auto 0 prf : IsJust (AbsFile.parse s)}
    -> File Abs
  fromString s = fromJust (parse s)

namespace RelFile
  ||| A quite strict function for parsing relative file paths.
  ||| This only accepts valid file bodies, so no doubling
  ||| of path separators or bodies starting with or ending
  ||| on whitespace. Sorry.
  public export
  parse : String -> Maybe (File Rel)
  parse s = case RelPath.parse s of
    Just (PRel $ sx :< x) => Just $ MkF (PRel sx) x
    _                     => Nothing

  public export
  fromString :
       (s : String)
    -> {auto 0 prf : IsJust (RelFile.parse s)}
    -> File Rel
  fromString s = fromJust (parse s)

--------------------------------------------------------------------------------
--          AnyFile
--------------------------------------------------------------------------------

||| A path (relative or absolute) in a file system.
public export
record AnyFile where
  constructor AF
  {0 pathType : PathType}
  file        : File pathType

public export %inline
Eq AnyFile where
  AF p1 == AF p2 = heq (toPath p1) (toPath p2)

public export
Ord AnyFile where
  compare (AF p1) (AF p2) = hcomp (toPath p1) (toPath p2)

export
Show AnyFile where show (AF p) = show p

export
Interpolation AnyFile where interpolate (AF p) = interpolate p

namespace AnyFile

  ||| Try and split a path into parent directory and
  ||| file/directory name.
  public export
  split : AnyFile -> (FilePath, Body)
  split (AF p) = let (f',b) := split p in (FP f', b)

  ||| Append a file ending to a path. If the path is empty,
  ||| this appends a hidden file/directory by prepending the
  ||| name with a dot.
  public export
  (<.>) : AnyFile -> (b : Body) -> AnyFile
  AF fp <.> s = AF $ fp <.> s

  ||| Checks whether an unknown path is absolute or not.
  export
  isAbsolute : AnyFile -> Bool
  isAbsolute (AF p) = isAbsolute p.parent

  ||| Tries to extract the basename from a path.
  export %inline
  basename : AnyFile -> Body
  basename = snd . split

  ||| Tries to extract the parent directory from a path.
  export
  parentDir : AnyFile -> FilePath
  parentDir = fst . split

  ||| Try and split a path into base name and file extension.
  export
  splitFileName : AnyFile -> Maybe (AnyFile, Body)
  splitFileName (AF p) = mapFst AF <$> splitFileName p

  ||| Try and split a path into the stem and extension
  ||| of the basename.
  export %inline
  stemAndExt : AnyFile -> Maybe (Body, Body)
  stemAndExt (AF p) = stemAndExt p

  ||| Try and extract the file stem from a path.
  export %inline
  fileStem : AnyFile -> Maybe Body
  fileStem (AF p) = fileStem p

  ||| Try and extract the extension from a file.
  export %inline
  extension : AnyFile -> Maybe Body
  extension (AF p) = extension p

  ||| True if the file's basename starts with a dot.
  export %inline
  isHidden : AnyFile -> Bool
  isHidden (AF p) = isHidden p
