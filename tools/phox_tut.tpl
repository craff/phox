function lit_correction(){
  print "....";
  getline;
  while( $0 !~ /\(\*->\*\)/ ) {
    getline;
  }
  getline;	
}

function lit_comment(){
  getline;
  while( $0 !~ /\(\*<-\*\)/ ) {
    getline;
  }
  getline;	
}

( $1 ~ /\(\*->\*\)/ ) {
  lit_correction();
} 

( $1 ~ /\(\*<-\*\)/ ) {
  lit_comment();
} 

( $1 !~ /\(\*(->)|(<-)\*\)/ ) {
  print $0;
}

