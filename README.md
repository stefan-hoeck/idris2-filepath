# idris2-filepath: Unix style file paths in Idris2

This library provides a convenient and safe API for working with
Unix style file paths. There are, however, some limitations:

* At the moment, paths starting with or ending on
  space characters are not supported.
  The following path will therefore not be parsed correctly:
  `"/oh_dear\ "`.

In the end, this should be comparable to `Libraries.Utils.Path`
from the Idris2 compiler API in terms of functionality (with the
big caveat that only Unix style paths are supported). However,
it performs *much* better.
