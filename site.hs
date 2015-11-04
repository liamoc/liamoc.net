--------------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}
import           Data.Monoid         ((<>))
import           Hakyll.Core.Compiler
import           Hakyll.Core.File
import           Hakyll.Core.Identifier
import           Hakyll.Core.Identifier.Pattern
import           Hakyll.Core.Item
import           Hakyll.Core.Metadata
import           Hakyll.Core.Routes
import           Hakyll.Core.Rules
import           Hakyll.Main
import           Hakyll.Web.CompressCss
import           Hakyll.Web.Feed
import           Hakyll.Web.Html.RelativizeUrls
import           Hakyll.Web.Pandoc
import           Hakyll.Web.Pandoc.Biblio -- BiblioWorkaround
import           Hakyll.Web.Tags
import           Hakyll.Web.Template
import           Hakyll.Web.Template.Context
import           Hakyll.Web.Template.List
import qualified Data.Map as M
import Text.Pandoc.Options
import Text.Pandoc
import System.IO.Unsafe
import System.Directory
import qualified Data.Set as S
import System.FilePath
import Agda.Interaction.Options (CommandLineOptions(..), defaultOptions)
import Image.LaTeX.Render.Pandoc
import Image.LaTeX.Render
import Data.Maybe
import Control.Exception (bracket)
import Network.URI
import AgdaSnippets

agdaOpts :: CommandLineOptions
agdaOpts = defaultOptions

readerSettings :: ReaderOptions
readerSettings = def { readerSmart = True, readerOldDashes = True, readerExtensions = S.insert Ext_pipe_tables pandocExtensions  }

writerSettings :: WriterOptions
writerSettings = def { writerHighlight = True }

defaultPreamble :: String
defaultPreamble = ""

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
main =
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

    let changeItemExtension :: (Item a -> Compiler (Item b)) -> Item a -> Compiler (Item b)
        changeItemExtension f i = let fn = toFilePath $ itemIdentifier i
                                   in do x <- f (i {itemIdentifier = fromFilePath $ fn -<.> "markdown" })
                                         return $ x {itemIdentifier = fromFilePath fn }

    match ("posts/*.markdown" .||. "posts/*.lagda" .||. "posts/*.org") $ do
        route $ setExtension "html"

        compile $ do

            m <- getMetadata =<< getUnderlying
            let latexPreamble = fromMaybe defaultPreamble $ M.lookup "preamble" m

            fp <-  flip replaceExtension "bib" . flip replaceDirectory "cites/" <$> getResourceFilePath
            readPandoc' <- if unsafePerformIO $ doesFileExist fp then do
                csl <- load "association-for-computing-machinery.csl"
                bib <- load (fromFilePath fp)
                return $ readPandocBiblio readerSettings csl bib
              else
                return $ readPandocWith readerSettings

            let writePandoc' = return . writePandocWith writerSettings

            i <- getResourceBody
            agdaCompiler agdaOpts i
              >>= changeItemExtension readPandoc'
              >>= texCompiler latexPreamble
              >>= writePandoc'
              >>= loadAndApplyTemplate "templates/post.html"    (tagsCtx tags)
              >>= saveSnapshot "content"
              >>= loadAndApplyTemplate "templates/disqus.html"  (tagsCtx tags)
              >>= loadAndApplyTemplate "templates/default.html" (tagsCtx tags)
              >>= relativizeUrls

    create ["archive.html"] $ do
        route idRoute
        compile $ do
            let archiveCtx = field "posts" (\_ -> postList' recentFirst)
                           <> constField "title" "Archives"
                           <> defaultContext

            makeItem ""
                >>= loadAndApplyTemplate "templates/archive.html" archiveCtx
                >>= loadAndApplyTemplate "templates/default.html" archiveCtx
                >>= relativizeUrls

    tagsRules tags $ \tag pattern -> do
        let title = "Posts tagged " ++ tag
        route idRoute
        compile $ do
            list <- postList tags pattern recentFirst
            makeItem ""
                >>= loadAndApplyTemplate "templates/archive.html"
                        (constField "title" title <>
                            constField "posts" list <>
                            defaultContext)
                >>= loadAndApplyTemplate "templates/default.html"
                        (constField "title" title <>
                            defaultContext)
                >>= relativizeUrls

    match "index.html" $ do
        route idRoute
        compile $ do
            let indexCtx = field "posts" (const $ postList' (\x -> take 3 <$> recentFirst x))
                         <> field "tagcloud" (const $ renderTagCloud 75 150 tags)
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




--------------------------------------------------------------------------------
postCtx :: Context String
postCtx =
    dateField "date" "%B %e, %Y" <>
    defaultContext

feedCtx :: Context String
feedCtx = postCtx <> bodyField "description"

--------------------------------------------------------------------------------
postList' :: ([Item String] -> Compiler [Item String]) -> Compiler String
postList' sortFilter = do
    posts   <- sortFilter =<< loadAll "posts/*"
    itemTpl <- loadBody "templates/post-item.html"
    applyTemplateList itemTpl postCtx posts

postList :: Tags -> Pattern -> ([Item String] -> Compiler [Item String])
         -> Compiler String
postList tags pattern preprocess' = do
    postItemTpl <- loadBody "templates/post-item.html"
    posts <- preprocess' =<< loadAll pattern
    applyTemplateList postItemTpl (tagsCtx tags) posts

tagsCtx :: Tags -> Context String
tagsCtx tags =
    tagsField "taglinks" tags <>
    postCtx

---
isAgda :: Item a -> Bool
isAgda i = ex == ".lagda"
  where ex = snd . splitExtension . toFilePath . itemIdentifier $ i

agdaCompiler :: CommandLineOptions -> Item String -> Compiler (Item String)
agdaCompiler aopt i =
     if isAgda i
          then cached cacheName $
               do fp <- getResourceFilePath
                  unsafeCompiler $ bracket getCurrentDirectory setCurrentDirectory $ const $
                      do abfp <- canonicalizePath fp
                         setCurrentDirectory (dropFileName abfp)
                         s <- renderAgdaSnippets aopt "Agda" (fromJust $ parseURIReference "/agda-lib/")  abfp
                         return $ i {itemBody = s}
          else return i
  where
    cacheName = "LiterateAgda.agdaCompiler"

---------
texCompiler :: String -> Item Pandoc -> Compiler (Item Pandoc)
texCompiler pre = withItemBody (unsafeCompiler . convertAllFormulaeDataURI 2 defaultEnv fopts)
     where fopts InlineMath = math { preamble = pre }
           fopts _          = displaymath { preamble = pre }
