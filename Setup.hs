#!/usr/bin/env runghc

module Main where

import Distribution.Simple
import System.Directory (copyFile)

main :: IO ()
main = copyFile "debian/changelog" "changelog" >>
       defaultMainWithHooks simpleUserHooks
