module FilePathProps

import Data.FilePath
import Data.SOP
import Data.Vect
import Hedgehog

%default total

--------------------------------------------------------------------------------
--          Generators
--------------------------------------------------------------------------------

bodyChar : Gen Char
bodyChar = frequency [(30, alphaNum), (1, element ['-', '_', '.'])]

body' : Gen String
body' = string (linear 1 20) bodyChar

body : Gen Body
body = fromMaybe "body" . body <$> body'

export
ending : Gen Body
ending = fromMaybe "txt" . body <$> string (linear 1 5) alphaNum

export
relDir : Gen (Path Rel)
relDir = PRel . (Lin <><) <$> list (linear 0 6) body

export
absDir : Gen (Path Abs)
absDir = PAbs . (Lin <><) <$> list (linear 0 6) body

export
dir : Gen FilePath
dir = choice [FP <$> absDir, FP <$> relDir]

export
file : Gen FilePath
file = [| dir <.> ending |]

export
relativeFile : Gen FilePath
relativeFile = [| (fromString <$> body') <.> ending |]

--------------------------------------------------------------------------------
--          Properties
--------------------------------------------------------------------------------

prop_split : Property
prop_split = property $ do
  [d, n] <- forAll $ np [dir,body]
  split (d /> n) === Just (d,n)

prop_splitFile : Property
prop_splitFile = property $ do
  [d, n,e] <- forAll $ np [dir,body,ending]
  split ((d /> n) <.> e) === Just (d,n <+> preDot e)

prop_roundtrip : Property
prop_roundtrip = property $ do
  f <- forAll file
  footnote (interpolate f)
  fromString (interpolate f) === f

prop_prependEmpty : Property
prop_prependEmpty = property $ do
  d <- forAll relDir
  ("" </> d) === FP d

prop_prependEmpty2 : Property
prop_prependEmpty2 = property $ do
  b <- forAll body
  (the FilePath "" /> b) === FP (PRel [<b])

prop_appendAssoc : Property
prop_appendAssoc = property $ do
  [x,y,z] <- forAll $ np [relDir, relDir, relDir]
  (x <+> (y <+> z)) === ((x <+> y) <+> z)

prop_appendLeftNeutral : Property
prop_appendLeftNeutral = property $ do
  x <- forAll relDir
  (neutral <+> x) === x

prop_appendRightNeutral : Property
prop_appendRightNeutral = property $ do
  x <- forAll relDir
  (x <+> neutral) === x

--------------------------------------------------------------------------------
--          Group
--------------------------------------------------------------------------------

export
props : Group
props = MkGroup "FilePath" [
        ("prop_split", prop_split)
      , ("prop_splitFile", prop_splitFile)
      , ("prop_roundtrip", prop_roundtrip)
      , ("prop_prependEmpty", prop_prependEmpty)
      , ("prop_prependEmpty2", prop_prependEmpty2)
      , ("prop_appendAssoc", prop_appendAssoc)
      , ("prop_appendLeftNeutral", prop_appendLeftNeutral)
      , ("prop_appendRightNeutral", prop_appendRightNeutral)
      ]
