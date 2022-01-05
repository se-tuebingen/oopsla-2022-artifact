module Proofs

  class Generator < Jekyll::Generator
    priority :normal

    def generate(site)
      pagesDB = site.pages.map do |page|
        id = page.url
               .chomp('index.html').chomp('.html').chomp('/')
               .reverse.chomp('/').reverse
        [id, page]
      end.to_h

      proofsIndex = pagesDB["proofs"]
      proofsPages = pagesDB.select { |id, page| id.start_with? "proofs/" }

      # coqdoc generates something like <h1 class=\"libtitle\">Top.SystemC.CaptureSets</h1>
      # so we need to extract the title from there if we do not want to modify coqdoc itself
      title_rx = /<h1 class="libtitle">([^<\/h1>]*)<\/h1>/

      proofsPages.each do |id, page|
        title_match = title_rx.match page.content
        unless title_match.nil?

          title = title_match[1]

          # This code is specific to this paper! Drop 'Top.' module prefix
          title = title.sub(/Top\./, '')

          # Only add titles to SystemC files, all others will be there, but hidden.
          if title.start_with? "SystemC"
            # Also drop SystemC module prefix
            title = title.sub(/SystemC\./, '')
            page.data['title'] = title
          end
          # Jekyll.logger.warn title_match[1]
        end
      end
    end

    def page(id, site)
      site.pages.find { |p| p.id == id }
    end
  end

end