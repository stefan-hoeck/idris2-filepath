module Main

import FilePathProps
import Hedgehog

%default total

main : IO ()
main = test [FilePathProps.props]
