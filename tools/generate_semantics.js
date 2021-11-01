module.paths.push('/usr/local/lib/node_modules');
const sem = require(process.env.FRET_PATH + '/fret-electron/app/parser/FretSemantics');
var input = JSON.parse(process.argv[2]);
input.forEach(x => {
  let res = sem.compile(x.fulltext);
  x.semantics = res.collectedSemantics;
});
console.log(JSON.stringify(input))
