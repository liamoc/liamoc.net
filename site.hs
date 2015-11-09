{-# LANGUAGE OverloadedStrings, LambdaCase #-}

import Data.Maybe
import Data.Monoid

import Image.LaTeX.Render
import Image.LaTeX.Render.Pandoc

import Network.URI

import System.Directory
import System.FilePath

import Text.Pandoc

import Hakyll
import Hakyll.Contrib.Agda
import Hakyll.Contrib.LaTeX

import qualified Data.Map as M
import qualified Data.Set as S

agdaOpts :: CommandLineOptions
agdaOpts = defaultOptions

agdaLibraryURI :: URI
Just agdaLibraryURI = parseURIReference "/agda-lib/"

readerSettings :: ReaderOptions
readerSettings = def { readerSmart = True
                     , readerOldDashes = True
                     , readerExtensions = S.insert Ext_pipe_tables pandocExtensions
                     }

writerSettings :: WriterOptions
writerSettings = def { writerHighlight = True }

defaultPreamble :: String
defaultPreamble = ""

formulaSettings :: String -> PandocFormulaOptions
formulaSettings pre
  = defaultPandocFormulaOptions
      { formulaOptions = \case DisplayMath -> displaymath { preamble = pre }
                               _           -> math        { preamble = pre }
      }

feedConfiguration :: FeedConfiguration
feedConfiguration = FeedConfiguration
    { feedTitle       = "liamoc.net"
    , feedDescription = "Musings of Liam O'Connor, lambda scientist"
    , feedAuthorName  = "Liam O'Connor"
    , feedAuthorEmail = "me@liamoc.net"
    , feedRoot        = "http://liamoc.net"
    }

--------------------------------------------------------------------------------
main :: IO ()
main = do
  renderEquations <- initFormulaCompilerDataURI 1000 defaultEnv
  hakyll $ do
    tags <- buildTags ("posts/*.markdown" .||. "posts/*.lagda" .||. "posts/*.org") (fromCapture "tags/*.html")

    match "images/*" $ do
      route   idRoute
      compile copyFileCompiler

    match "agda-lib/*" $ do
      route   idRoute
      compile copyFileCompiler

    match "js/*" $ do
      route   idRoute
      compile copyFileCompiler

    match "js/patterns/*" $ do
      route   idRoute
      compile copyFileCompiler

    match "css/*" $ do
      route   idRoute
      compile compressCssCompiler

    match (fromList ["about.rst", "contact.markdown"]) $ do
      route   $ setExtension "html"
      compile $ pandocCompiler
            >>= loadAndApplyTemplate "templates/default.html" defaultContext
            >>= relativizeUrls

    match "cites/*.bib" $ compile biblioCompiler
    match "association-for-computing-machinery.csl" $ compile cslCompiler


    match ("posts/*.markdown" .||. "posts/*.lagda" .||. "posts/*.org") $ do
      route $ setExtension "html"

      compile $ do
        pr <- fmap (fromMaybe defaultPreamble . M.lookup "preamble") (getMetadata =<< getUnderlying)
        fp <- flip replaceExtension "bib" . flip replaceDirectory "cites/" <$> getResourceFilePath

        let readPandoc' i = do
              exists <- unsafeCompiler $ doesFileExist fp
              if exists then do
                csl <- load "association-for-computing-machinery.csl"
                bib <- load (fromFilePath fp)
                readPandocBiblio readerSettings csl bib i
              else
                readPandocWith readerSettings i

            writePandoc' = return . writePandocWith writerSettings

        getResourceBody
          >>= readLiterateAgda agdaOpts agdaLibraryURI
          >>= defaultFileType Markdown readPandoc'
          >>= renderEquations (formulaSettings pr)
          >>= writePandoc'
          >>= loadAndApplyTemplate "templates/post.html"    (tagsCtx tags)
          >>= saveSnapshot "content"
          >>= loadAndApplyTemplate "templates/disqus.html"  (tagsCtx tags)
          >>= loadAndApplyTemplate "templates/default.html" (tagsCtx tags)
          >>= relativizeUrls

    create ["archive.html"] $ do
      route idRoute
      compile $ do
        let archiveCtx = mconcat [ field "posts" $ const $ postList' recentFirst
                                 , constField "title" "Archives"
                                 , defaultContext
                                 ]

        makeItem ""
          >>= loadAndApplyTemplate "templates/archive.html" archiveCtx
          >>= loadAndApplyTemplate "templates/default.html" archiveCtx
          >>= relativizeUrls

    tagsRules tags $ \tag pattern -> do
      route idRoute
      compile $ do
        list <- postList (tagsCtx tags) pattern recentFirst
        let title    = "Posts tagged " ++ tag
            titleCtx = constField "title" title <> defaultContext
            tagCtx   = mconcat [ constField "title" title
                               , constField "posts" list
                               , defaultContext
                               ]
        makeItem ""
          >>= loadAndApplyTemplate "templates/archive.html" tagCtx
          >>= loadAndApplyTemplate "templates/default.html" titleCtx
          >>= relativizeUrls

    match "index.html" $ do
      route idRoute
      compile $ do
        let indexCtx = mconcat [ field "posts"    $ const $ postList' $ fmap (take 3) . recentFirst
                               , field "tagcloud" $ const $ renderTagCloud 75 150 tags
                               ]
        getResourceBody
          >>= applyAsTemplate indexCtx
          >>= loadAndApplyTemplate "templates/default.html" postCtx
          >>= relativizeUrls

    create ["atom.xml"] $ do
      route idRoute
      compile $ do
        posts <- take 10  <$> (recentFirst =<< loadAllSnapshots "posts/*" "content")
        renderAtom feedConfiguration feedCtx posts

    create ["rss.xml"] $ do
      route idRoute
      compile $ do
        posts <- take 10 <$> (recentFirst =<< loadAllSnapshots "posts/*" "content")
        renderRss feedConfiguration feedCtx posts

    match "templates/*" $ compile templateCompiler
  where
    tagsCtx tags = tagsField "taglinks" tags <> postCtx

    postCtx = dateField "date" "%B %e, %Y" <> defaultContext
    feedCtx = postCtx <> bodyField "description"

    postList' = postList postCtx "posts/*"

    postList ctx pattern prep = do
      posts <- prep =<< loadAll pattern
      itemTpl <- loadBody "templates/post-item.html"
      applyTemplateList itemTpl ctx posts




