--------------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}
import Data.Monoid (mappend)
import Hakyll
    ( Context,
      hakyll,
      match,
      route,
      idRoute,
      compile,
      copyFileCompiler,
      compressCssCompiler,
      fromList,
      setExtension,
      pandocCompiler,
      loadAndApplyTemplate,
      defaultContext,
      relativizeUrls,
      create,
      recentFirst,
      loadAll,
      listField,
      constField,
      makeItem,
      getResourceBody,
      applyAsTemplate,
      templateBodyCompiler,
      dateField,
      saveSnapshot,
      loadAllSnapshots,
      fromCapture,
      renderRss,
      buildTags,
      bodyField,
      Configuration,
      destinationDirectory,
      hakyllWith,
      defaultConfiguration,
      FeedConfiguration(..) )


--------------------------------------------------------------------------------
myFeedConfiguration :: FeedConfiguration
myFeedConfiguration = FeedConfiguration
    { feedTitle       = "Mind→Theory→Math→Code"
    , feedDescription = "Seeking a Language for Theoretical Psychology"
    , feedAuthorName  = "Britt Anderson"
    , feedAuthorEmail = "britt@uwaterloo.ca"
    , feedRoot        = "https://brittAnderson.github.io"
    }

config :: Configuration
config = defaultConfiguration
  { destinationDirectory = "docs"
  }

main :: IO ()
main = hakyllWith config $ do

  --something about tags will eventually go here
  
  match "images/*" $ do
    route   idRoute
    compile copyFileCompiler
  
  match "css/*" $ do
    route   idRoute
    compile compressCssCompiler
  
  match (fromList ["about.markdown", "contact.markdown"]) $ do
    route   $ setExtension "html"
    compile $ pandocCompiler
      >>= loadAndApplyTemplate "templates/default.html" defaultContext
      >>= relativizeUrls
  
  match "posts/*" $ do
    route $ setExtension "html"
    compile $ pandocCompiler
      >>= loadAndApplyTemplate "templates/post.html"    postCtx
      >>= saveSnapshot "content"
      >>= loadAndApplyTemplate "templates/default.html" postCtx
      >>= relativizeUrls
  
  create ["archive.html"] $ do
    route idRoute
    compile $ do
      posts <- recentFirst =<< loadAll "posts/*"
      let archiveCtx =
              listField "posts" postCtx (return posts) `mappend`
              constField "title" "Archives"            `mappend`
              defaultContext
      
      makeItem ""
          >>= loadAndApplyTemplate "templates/archive.html" archiveCtx
          >>= loadAndApplyTemplate "templates/default.html" archiveCtx
          >>= relativizeUrls
  
  create ["rss.xml"] $ do
    route idRoute
    compile $ do
      let feedCtx = postCtx `mappend` bodyField "description"
      posts <- fmap (take 10) . recentFirst =<< loadAllSnapshots "posts/*" "content"
      renderRss myFeedConfiguration feedCtx posts
     
  match "index.html" $ do
    route idRoute
    compile $ do
      posts <- recentFirst =<< loadAll "posts/*"
      let indexCtx =
            listField "posts" postCtx (return posts) `mappend`
            defaultContext
      
      getResourceBody
        >>= applyAsTemplate indexCtx
        >>= loadAndApplyTemplate "templates/default.html" indexCtx
        >>= relativizeUrls
  
  match "templates/*" $ compile templateBodyCompiler



--------------------------------------------------------------------------------
postCtx :: Context String
postCtx =
    dateField "date" "%B %e, %Y" `mappend`
    defaultContext
