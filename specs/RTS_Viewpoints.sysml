import Views::*;

package 'RTS Viewpoints and Views' {
  import 'RTS Stakeholders'::*;

  // Viewpoints and view definitions specify the different points of view
  // that a system may be viewed from, and which parts of the system model
  // attend to each view.  We will specify viewpoints for a few kinds
  // of NRC actors, various kinds of HARDENS performers, various kinds of
  // other Galois employees who are interested in this project and its
  // outcomes, and other government and industry parties interested in RDE.
  
  viewpoint 'NRC General Customer Viewpoint' {}

  view def 'NRC General Customer View Definition' {}  
  
  viewpoint 'NRC Assurance Customer Viewpoint' {}
  
  view def 'NRC Assurance Customer View Definition' {}
  
  viewpoint 'Galois Performer Viewpoint' {}
  
  view def 'Galois Performer View Definition' {}
  
  view 'Galois PI View' : 'Galois Performer View Definition' {}
  
  view 'Galois PL View' : 'Galois Performer View Definition' {}

  view 'Galois Software Engineer View' : 'Galois Performer View Definition' {}
  
  view 'Galois Hardware Engineer View' : 'Galois Performer View Definition' {}
  
  view 'Galois Assurance Engineer View' : 'Galois Performer View Definition' {}
  
  viewpoint 'Galois Principal View' {}
  
  viewpoint 'Galois Executive View' {}
  
  viewpoint 'Galois Customer Specialist View' {}
  
  viewpoint 'Galois Research Engineering View' {}
  
  viewpoint 'General Party interested in Rigorous Digital Engineering' {}   
}