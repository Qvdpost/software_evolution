module vis::visualize

import IO;
import Set;
import List;
import Map;
import lang::java::m3::Core;
import lang::java::m3::AST;
import lang::java::jdt::m3::Core;
import lang::java::jdt::m3::AST;

import salix::App;
import salix::HTML;

alias Model = tuple[int count];

Model init() = <0>;

SalixApp[Model] counterApp(str id = "root") = makeApp(id, init, view, update);

App[Model] counterWebApp()
  = webApp(
      counterApp(),
      |project://series_1/src/vis/index.html|, 
      |project://series_1/src|
    );

data Msg
  = inc()
  | dec()
  ;

Model update(Msg msg, Model m) {
  switch (msg) {
    case inc(): m.count += 1;
    case dec(): m.count -= 1;
  }
  return m;
}

void view(Model m) {
  div(() {
    
    h2("My first bar chart app in Rascal");
    
    button(onClick(inc()), "+");
    
    div("<m.count>");
    
    button(onClick(dec()), "-");

  });
}

