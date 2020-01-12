function dump(o)
   if type(o) == 'table' then
      local s = '{ '
      for k,v in pairs(o) do
         if type(k) ~= 'number' then k = '"'..k..'"' end
         s = s .. '['..k..'] = ' .. dump(v) .. ','
      end
      return s .. '} '
   else
      return tostring(o)
   end
end
function file_exists(name)
   local f=io.open(name,"r")
   if f~=nil then io.close(f) return true else return false end
end
summary = nil
flag = false
return {
  {
    Note = function(para) 
       flag = true
    end,
    Para = function(para) 
       if flag then
         flag = false
       else 
         summary = summary or pandoc.utils.stringify(para)
         if summary == "" then summary = nil end
       end
    end,
    Pandoc = function(pdoc)
      id = "http://liamoc.net/" .. string.gsub(PANDOC_STATE.input_files[1],"%..*","") .. "/index.html"
      iso_date = string.match(PANDOC_STATE.input_files[1],"2%d%d%d%-%d%d%-%d%d") or "1970-01-01"
      iso_time = string.match(pandoc.utils.stringify(pdoc.meta.time or "00:00"), "%d%d%:%d%d") or "00:00"
      title = pandoc.utils.stringify(pdoc.meta.title)
      updated = iso_date .. "T" .. iso_time .. ":00Z"
      entry = string.format([[<entry>
                                <id>%s</id>
                                <title>%s</title>
                                <updated>%s</updated>
                                <content src="%s" /><link rel="alternate" href="%s"/>
                                <summary><![CDATA[%s]] .. "]]></summary></entry>\n", id, title, updated, id, id, summary)
      if not file_exists("out/atom.xml") then 
         file = io.open("out/atom.xml", "w")
         io.output(file)
         header = string.format([[<?xml version="1.0" encoding="utf-8"?>
                                 <feed xmlns="http://www.w3.org/2005/Atom">
                                 <title>liamoc.net</title>
                                 <link rel="alternate" href="http://liamoc.net/"/>
                                 <link rel="self" href="http://liamoc.net/atom.xml"/>
                                 <updated>%s</updated>
                                 <author>
                                   <name>Liam O'Connor</name>
                                 </author>
                                 <id>http://liamoc.net</id>]] .. "\n",updated)
         io.write(header)
         io.close(file)
      end
      file = io.open("out/atom.xml","a")
      io.output(file)
      io.write(entry)
      io.close(file)
      return pandoc.Pandoc({})
    end,
  }
}
