PANDOC=pandoc
AGDA=agda
RUNHASKELL=runhaskell


start: all


#induces a dependency on chronic from moreutils.. feel free to just make this blank and deal with some spam from Agda.
SUPPRESS_AGDA=chronic
SUPPRESS=>/dev/null

STATICS=$(wildcard images/*) css/default.css js/details.polyfill.min.js
POST_FILES=$(shell find -E posts -maxdepth 1 -regex '.*(\.lagda\.org|\.lagda\.md|\.org|\.md)$$' -type f | sort -r)
POSTS=$(shell echo $(POST_FILES) | sed 's/\.[^\s]*$$/ /g' | sed 's/\.[^\s]* / /g' | sed "s/posts\///g")
COMPUTERS=$(wildcard images/comp*)

BLUE=$(shell tput setaf 4)
PALEBLUE=$(shell tput setaf 12)
GREY=$(shell tput setaf 8)
BOLD=$(shell tput bold)
GREEN=$(shell tput setaf 10)
YELLOW=$(shell tput setaf 3)
PURPLE=$(shell tput setaf 5)
SGR0=$(shell tput sgr0)

-include tag_list

-include $(POSTS:%=dependencies/%.d)


$(COMPUTERS:images/comp%=out/thumbnails/%): out/thumbnails/%: images/comp%
	@echo '$(PALEBLUE)Generating thumbnail for $(BOLD)$<$(SGR0)'
	@mkdir -p $(@D)  && convert $< -resize 500 $@
	

$(STATICS:%=out/%): out/%: %
	@echo '$(PALEBLUE)Copying static file $(BOLD)$<$(SGR0)'
	@mkdir -p $(@D) && cp $< $@

all: $(POSTS:%=out/posts/%/index.html) $(TAGS:%=out/tags/%.html) $(COMPUTERS:images/comp%=out/thumbnails/%) out/index.html out/computers.html out/work_with_me.html out/contact.html out/publications.html out/posts/archive.html out/atom.xml $(STATICS:%=out/%)

preview:
	@cd out && python -m SimpleHTTPServer 8000

clean:
	@rm -rf tags out dependencies tag_list tag_cloud.html post_list.md

publish:
	@echo '$(BOLD)$(GREEN)Uploading to liamoc.net$(SGR0)'
	@cd out && rsync -rv * liamoc.net:~/public_html	

dependencies/%.d: posts/%.md dependencies.lua
	@echo '$(BOLD)$(@F:%.d=%):$(SGR0) $(BLUE)Scanning for dependencies$(SGR0)'
	@mkdir -p $(@D) && rm -f $@
	@$(PANDOC) $< -t plain --lua-filter=dependencies.lua $(SUPPRESS)

dependencies/%.d: posts/%.lagda.md dependencies.lua
	@echo '$(BOLD)$(@F:%.d=%):$(SGR0) $(BLUE)Scanning for dependencies$(SGR0)'
	@mkdir -p $(@D) && rm -f $@
	@$(PANDOC) $< -t plain --lua-filter=dependencies.lua $(SUPPRESS)

dependencies/%.d: posts/%.org dependencies.lua
	@echo '$(BOLD)$(@F:%.d=%):$(SGR0) $(BLUE)Scanning for dependencies$(SGR0)'
	@mkdir -p $(@D) && rm -f $@
	@$(PANDOC) $< -t plain --lua-filter=dependencies.lua $(SUPPRESS)

dependencies/%.d: posts/%.lagda.org dependencies.lua
	@echo '$(BOLD)$(@F:%.d=%):$(SGR0) $(BLUE)Scanning for dependencies$(SGR0)'
	@mkdir -p $(@D) && rm -f $@
	@$(PANDOC) $< -t plain --lua-filter=dependencies.lua $(SUPPRESS)


tag_list: $(POST_FILES) 
	@echo '$(BLUE)Scanning for $(BOLD)tags$(SGR0)'
	@rm -rf tags
	@for post in $^; do \
          echo "$(GREY)  scanning:$(SGR0) " $$post; \
          $(PANDOC) $$post -t plain --lua-filter=keywords.lua $(SUPPRESS);\
        done
	@echo TAGS= `ls tags | sed s/.md//g` > tag_list

tags/%.md: tag_list

tag_cloud.html: tag_list clouds.hs
	@echo 'Generating $(BOLD)tag cloud$(SGR0)'
	@wc -l tags/* | grep md | $(RUNHASKELL) clouds.hs > tag_cloud.html

out/atom.xml: $(POST_FILES)
	@echo 'Generating $(BOLD)atom feed$(SGR0)'
	@rm -f out/atom.xml
	@for post in $^; do \
          echo "$(GREY)  entry for:$(SGR0) " $$post; \
          $(PANDOC) $$post -t plain --lua-filter=atom_entry.lua $(SUPPRESS);\
        done
	@echo '</feed>' >> out/atom.xml 

post_list.md: $(POST_FILES)
	@echo 'Generating $(BOLD)archive list$(SGR0)'
	@rm -f post_list.md
	@for post in $^; do\
          echo "$(GREY)  entry for:$(SGR0) " $$post; \
          $(PANDOC) $$post -t plain --lua-filter=post_list.lua $(SUPPRESS);\
        done

out/index.html: index.md post_list.md index_conclusion.md tag_cloud.html
	@echo 'Generating $(BOLD)index.html$(SGR0)'
	@mkdir -p $(@D) && cat post_list.md | head -6 | tail -3 \
          | $(PANDOC) -s -T "liamoc.net" --data-dir=. -t html5 \
                      $< /dev/stdin index_conclusion.md tag_cloud.html -o $@ $(SUPPRESS)
out/computers.html: computers.md
	@echo 'Generating $(BOLD)computers.html$(SGR0)'
	@mkdir -p $(@D) && $(PANDOC) -s -T "liamoc.net" --data-dir=. -t html5 $< -o $@ $(SUPPRESS)

out/work_with_me.html: work_with_me.md
	@echo 'Generating $(BOLD)work_with_me.html$(SGR0)'
	@mkdir -p $(@D) && $(PANDOC) -s -T "liamoc.net" --data-dir=. -t html5 $< -o $@ $(SUPPRESS)

out/contact.html: contact.md
	@echo 'Generating $(BOLD)contact.html$(SGR0)'
	@mkdir -p $(@D) && $(PANDOC) -s -T "liamoc.net" --data-dir=. -t html5 $< -o $@ $(SUPPRESS)

out/publications.html: publications.org
	@echo 'Generating $(BOLD)publications.html$(SGR0)'
	@mkdir -p $(@D) && $(PANDOC) -s -T "liamoc.net" --data-dir=. -t html5 $< -o $@ $(SUPPRESS)

out/posts/archive.html: post_list.md
	@echo 'Generating $(BOLD)archive.html$(SGR0)'
	@mkdir -p $(@D) && $(PANDOC) -s -T "liamoc.net" --data-dir=. -t html5 $< -o $@ $(SUPPRESS)
out/tags/%.html: tags/%.md
	@echo 'Generating $(BOLD)tags/$(@F)$(SGR0)'
	@mkdir -p $(@D) && $(PANDOC) -s -T "liamoc.net" --data-dir=. -t html5 $< -o $@ $(SUPPRESS)

posts/%.bib: default.bib
	@echo '$(BOLD)$(@F:.bib=):$(SGR0) $(YELLOW)Using default bibliography$(SGR0)'
	@cp default.bib $@
posts/%.preamble: default_preamble
	@echo '$(BOLD)$(@F:.preamble=):$(SGR0) $(YELLOW)Using default preamble$(SGR0)'
	@cp default_preamble $@

out/posts/%/cites.bib: posts/%.bib 
	@mkdir -p $(@D) && cp $< $@
out/posts/%/preamble: posts/%.preamble
	@mkdir -p $(@D) && cp $< $@


out/posts/%/index.lagda.md: posts/%.lagda.md 
	@mkdir -p $(@D) && cp $< $@
out/posts/%/index.lagda.org: posts/%.lagda.org
	@mkdir -p $(@D) && cp $< $@
out/posts/%/index.org: posts/%.org
	@mkdir -p $(@D) && cp $< $@
out/posts/%/index.md: posts/%.md
	@mkdir -p $(@D) && cp $< $@
out/posts/%/index.md: out/posts/%/index.lagda.md 
	@echo "$(BOLD)`basename $(@D)`:$(SGR0) $(PURPLE)Running agda$(SGR0)"
	@cd $(@D); \
        cp $(<F) `basename $(@D)`.lagda.md \
        && $(SUPPRESS_AGDA) $(AGDA) --html --html-dir=. --html-highlight=auto `basename $(@D)`.lagda.md \
        && cat `basename $(@D)`.md | sed "s/`basename $(@D)`.html/index.html/g" > index.md; rm -f `basename $(@D)`.lagda.md

out/posts/%/index.org: out/posts/%/index.lagda.org
	@echo "$(BOLD)`basename $(@D)`:$(SGR0) $(PURPLE)Running agda$(SGR0)"
	@cd $(@D); \
        cp $(<F) `basename $(@D)`.lagda.org \
        && $(SUPPRESS_AGDA) $(AGDA) --html --html-dir=. --html-highlight=auto `basename $(@D)`.lagda.org \
        && cat `basename $(@D)`.md | sed "s/`basename $(@D)`.html/index.html/g" > index.org; rm -f `basename $(@D)`.lagda.org


out/posts/%/index.html: out/posts/%/index.md out/posts/%/cites.bib out/posts/%/preamble
	@echo "$(BOLD)`basename $(@D)`:$(SGR0) Generating post html"
	@cd $(@D) \
        && $(PANDOC) -c "Agda.css" -s -T "liamoc.net" --lua-filter=../../../math.lua \
                     --data-dir=../../.. -t html5 --highlight-style=tango $(<F) \
                     --citeproc --bibliography cites.bib --csl ../../../cambridge-university-press-author-date.csl  \
                     -o $(@F) $(SUPPRESS)

out/posts/%/index.html: out/posts/%/index.org out/posts/%/cites.bib out/posts/%/preamble
	@echo "$(BOLD)`basename $(@D)`:$(SGR0) Generating post html"
	@cd $(@D) \
        && $(PANDOC) -c "Agda.css" -s -T "liamoc.net" --lua-filter=../../../math.lua \
                     --data-dir=../../.. -t html5 --highlight-style=tango $(<F) \
                     --citeproc --bibliography cites.bib --csl ../../../cambridge-university-press-author-date.csl \
                     -o $(@F) $(SUPPRESS)

