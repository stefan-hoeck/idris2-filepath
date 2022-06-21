# idris2-filepath: Unix style file paths in Idris2

This library provides a convenient and safe API for working with
Unix style file paths. There are, however, some limitations:

* At the moment, paths starting with or ending on (escaped)
  space characters are not supported.
  The following path fill therefore not be parsed correctly:
  `"/oh_dear\ "`.
* Paths with parent directory tokens (`..`) in the middle will
  not be parsed correctly: The path `foo/../bar` will be parsed
  as `foo/bar`. This is out of laziness (of myself) not out of
  necessity.
