open CSP_Alloy;

val wrPreamble = "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n"^
  "<graphml xmlns=\"http://graphml.graphdrawing.org/xmlns\"\n"^
    "xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\"\n"^
    "xsi:schemaLocation=\"http://graphml.graphdrawing.org/xmlns\n"^
     "http://graphml.graphdrawing.org/xmlns/1.0/graphml.xsd\">\n"

(*Code prints to enable the translation of PDGs into GraphML*)
val wrStartGraph = "<graph id=\"PDG\" edgedefault=\"directed\">\n"
val wrEndGraph = "</graph>\n"^
  "</graphml>\n"

fun wrNode v = "<node id=\""^charsToStr(v)^"\"/>\n"
fun wrNodes [] = ""
  | wrNodes (v::vs) = (wrNode v)^(wrNodes vs)

fun wrEdge pdg e =
  let val g = toGr pdg in
    "<edge id=\""^charsToStr(e)^"\" source=\""^charsToStr(the(src g e))^"\" target=\""^charsToStr(the(tgt g e))^"\"/>\n"
  end
fun wrEdges [] pdg = ""
  | wrEdges (e::es) pdg = (wrEdge pdg e)^(wrEdges es pdg)

fun toGraphML pdg =
  wrPreamble^wrStartGraph^(wrNodes (nsG pdg))^(wrEdges (esG pdg) pdg)^wrEndGraph
