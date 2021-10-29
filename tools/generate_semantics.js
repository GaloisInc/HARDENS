module.paths.push('/usr/local/lib/node_modules');
const sem = require(process.env.FRET_PATH + '/fret-electron/app/parser/FretSemantics');

var NodePouchDB = require('pouchdb');
NodePouchDB.plugin(require('pouchdb-find'));
var userDocumentsFolder = '/Users/abakst/Documents';
var leveldbDB = new NodePouchDB(userDocumentsFolder + '/fret-db');
var modelDB = new NodePouchDB(userDocumentsFolder + '/model-db');
leveldbDB.info().then(function (info) {
//  console.log('We can use PouchDB with LevelDB!');
}).catch(function (err) {
  console.error('Error for LevelDB');
  console.error(err);
});

modelDB.info().then(function (info){
}).catch(function (err) {
//  console.log('Error for modelDB');
  console.error(err);
})


var input = process.argv[2];

const res = sem.compile(input);

console.log(JSON.stringify(res));
// variables = res.collectedSemantics.variables;
// modelDB.find({
//       selector: {
//         project: "New", //selectedVariable.project,
//         component_name: "FSM", //selectedVariable.component_name,
//         modeldoc: false
//       }
//     }).then(function(result){
//       if(result.docs.length != 0){
//         variables.forEach(function(v){
//           a = result.docs.find(r => r.variable_name === v)
//           if (a){
//             console.log("existing variable")
//             console.log(a)
//           }
//           else {
//             console.log("Non existing variable")
//           }
//         })
//       }
//     })
