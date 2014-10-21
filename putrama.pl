#!/usr/bin/env perl

## mainly Copyright © 2009-2014 by Daniel Friesel <derf@finalrewind.org>
## License: WTFPL <http://sam.zoy.org/wtfpl>
##   0. You just DO WHAT THE FUCK YOU WANT TO.
##
## hacked by Aydin Demircioglu <putrama /at/ cloned.de>
## License: MIT (rough WTFPL equivalent)

use strict;
use warnings;
use 5.010;

no if $] >= 5.018, warnings => "experimental::smartmatch";

use utf8;


BEGIN {push @INC, '.'}

use Geo::KML::PolyMap qw(generate_kml_file generate_kmz_file);
use WWW::EFA::Request;
use WWW::EFA::LocationFactory;
use Math::Round;
use Time::Local;

use XML::LibXML;
use LWP::UserAgent;
 
use MooseX::Params::Validate;

use YAML;
use Carp;
use Try::Tiny;
use File::Spec::Functions;
use XML::LibXML;
use Class::Date qw/now/;


use Encode qw(decode);
use Travel::Routing::DE::EFA;
use Exception::Class;
use Getopt::Long qw/:config no_ignore_case/;
use List::Util qw(first);

# --- header
	our $VERSION = '1.0';
	print ("\n");
	print ("putrama v$VERSION\n");
	print ("    public transport map generator.\n");
	print ("\n");

my $ignore_info = 'Fahrradmitnahme';
my $efa;
my $efa_url = 'http://efa.vrr.de/vrr/XSLT_TRIP_REQUEST2';
my ( @from, @to, @via, $from_type, $to_type, $via_type );
my $opt = {
	'efa-url'     => \$efa_url,
	'help'        => sub { show_help(0) },
	'ignore-info' => \$ignore_info,
	'from'        => \@from,
	'to'          => \@to,
	'version'     => sub { say "efa version $VERSION"; exit 0 },
	'via'         => \@via,
};
my $polygonList = [];

# --- options
	my $startcolor = "A00000FF";
	my $endcolor ="A0FF0000";
	my $kmlfilename = "./test.kml";;
	my $verboisty = 20;


binmode( STDOUT, ':encoding(utf-8)' );
binmode( STDERR, ':encoding(utf-8)' );


	# tool to get a proper  date
	sub convertDate
	{
		my $day = pop;
		my $month = pop;
		my $year = pop;

		my $hinfahrt = timegm(0,0,11,$day,$month-1,$year);
		#print "Time for date $year-$month-$day: $hinfahrt\n";

		$_ = $hinfahrt;
	}


sub show_help {
	my ($exit_status) = @_;

	say 'Usage: efa [options] <from-city> <from-stop> <to-city> <to-stop>';
	say 'See also: man efa';

	exit $exit_status;
}

sub handle_efa_exception {
	my ($e) = @_;

	if ( $e->isa('Travel::Routing::DE::EFA::Exception::Setup') ) {
		if ( $e->message ) {
			printf STDERR (
				"Error: %s (option '%s'): %s\n",
				$e->description, $e->option, $e->message
			);
		}
		else {
			printf STDERR (
				"Error: %s (option '%s', got '%s', want '%s')\n",
				$e->description, $e->option, $e->have, $e->want
			);
		}

		exit 1;
	}
	if ( $e->isa('Travel::Routing::DE::EFA::Exception::Net') ) {
		printf STDERR ( "Error: %s: %s\n", $e->description,
			$e->http_response->as_string );
		exit 2;
	}
	if ( $e->isa('Travel::Routing::DE::EFA::Exception::NoData') ) {
		printf STDERR ( "Error: %s\n", $e->description );
		exit 3;
	}
	if ( $e->isa('Travel::Routing::DE::EFA::Exception::Ambiguous') ) {
		printf STDERR (
			"Error: %s for key %s. Specify one of %s\n",
			$e->description, $e->post_key, $e->possibilities
		);
		exit 4;
	}
	if ( $e->isa('Travel::Routing::DE::EFA::Exception::Other') ) {
		printf STDERR ( "Error: %s: %s\n", $e->description, $e->message );
		exit 5;
	}

	printf STDERR ( "Uncaught exception: %s\n%s", ref($e), $e->trace );
	exit 10;
}

sub check_for_error {
	my ($eval_error) = @_;

	if ( not defined $efa ) {
		if (    $eval_error
			and ref($eval_error)
			and $eval_error->isa('Travel::Routing::DE::EFA::Exception') )
		{
			handle_efa_exception($eval_error);
		}
		elsif ($eval_error) {
			printf STDERR
			  "Unknown Travel::Routing::DE::EFA error:\n${eval_error}";
			exit 10;
		}
		else {
			say STDERR 'Travel::Routing::DE::EFA failed to return an object';
			exit 10;
		}
	}

	return;
}



# Private method to wrap around:
#  * the http request to the EFA server
#  * parse the XML content
#  * error handling if any of the above fail or are unexpected
# Returns the XML as got from the EFA server
sub get_xml {
    my ( %params ) = validated_hash(
        \@_,
        request      => { isa => 'WWW::EFA::Request'   },
    );

    my $xml;
    # If the XML source is defined, use it rather than a live request
    my $cache_file = undef;

    if( $cache_file and -f $cache_file ){
        # TODO: RCL 2011-11-20 add debug
        # printf "#RCL reading from: %s\n", $cache_file;
        open( my $fh_in, '<:encoding(ISO-8859-1)', $cache_file ) or die( $! );
        while( my $line = readline( $fh_in ) ){
            $xml .= $line;
        }
        close $fh_in;
    }else{
        sleep(1);

        my $agent = LWP::UserAgent->new();



        # Use post - it is more robust than GET, and we don't have to encode parameters
        my $result = $agent->post( $params{request}->url, $params{request}->arguments );
        
        # If response code is not 2xx, something went wrong...
        if( not $result->is_success ){
            croak( "Response from posting request for stop_finder was not a success:\n" . Dump( {
                    URL       => $result->request->uri,
                    Status    => $result->code,
                    Content   => $result->decoded_content,
                    } ) );
        }
        $xml = $result->decoded_content;
        
        if( $cache_file ){
            # TODO: RCL 2011-11-13 Do all operators send in ISO-8859-1 encoding?
            open( my $fh_out, '>:encoding(ISO-8859-1)', $cache_file ) or die( $! );
            print $fh_out $xml;
            close $fh_out;
        }
    }

    return $xml;
}




# Private method to wrap around:
#  * get_xml
#  * make L<XML::LibXML> parser
#  * move to the /itdRequest element in the document
# Returns a L<XML::LibXML> document
sub get_doc { 
    my( %params ) = validated_hash(
        \@_,
        request => { isa => 'WWW::EFA::Request' },        
        );

    my $xml = get_xml( %params );

    my $parser = XML::LibXML->new();
    my $doc = $parser->parse_string( $xml, ) or croak( "Could not read XML" );

    # We always want to be in the itdRequest section
    ( $doc ) = $doc->findnodes( '/itdRequest' );

    return $doc;
}


sub coord_request {
	# get parameter
    my $base_url = "http://efa.vrr.de/vrr/";
    my $longitude = $_[1];
    my $latitude = $_[2];
    
    my $max_results = 3;
    my $max_distance = 1320;

#    print "Trying to dissolve $longitude, $latitude\n";

    # Build the request
    my $req = WWW::EFA::Request->new(
        base_url        => $base_url,
        service         => 'XML_COORD_REQUEST',
    );

    $req->set_argument( 'coordListOutputFormat' , 'STRING'              );
    $req->set_argument( 'type_1'                , 'STOP'                );
    $req->set_argument( 'inclFilter'            , 1                     );
    $req->set_argument( 'max'                   , $max_results  );
    $req->set_argument( 'radius_1'              , $max_distance );
    # Cannot use the $req->add_location method here because it would add the location by id
    $req->set_argument( 'coord'                 , sprintf( "%.6f:%.6f:WGS84", 
            $longitude,
            $latitude,
            ) );

    my $doc = get_doc( request => $req );

    # Move into the itdDepartureMonitorRequest element
    ( $doc ) = $doc->findnodes( 'itdCoordInfoRequest' );
    
    my @locations;
    my $location_factory = WWW::EFA::LocationFactory->new();

    foreach my $coord_elem( $doc->findnodes( 'itdCoordInfo/coordInfoItemList/coordInfoItem' ) ){
        my $location = $location_factory->location_from_coordInfoItem( $coord_elem );
        push( @locations, $location );
#print " -".$location->name.", ".$location->locality.", ".$location->id."\n";
    }

	#print "  Found ". $locations[0]->name. "/". $locations[0]->locality."\n";
    return ($locations[0]->name, $locations[0]->locality, $locations[0]->distance);
}



sub display_connection {
	my ($c) = @_;

	if ( $c->delay ) {
		printf( "# +%d,  scheduled: %s -> %s\n",
			$c->delay, $c->departure_stime, $c->arrival_stime );
	}

	for my $extra ( $c->extra ) {

		if ( not( length $ignore_info and $extra =~ /$ignore_info/i ) ) {
			say "# $extra";
		}
	}

	if ( $opt->{maps} ) {
		for my $m ( $c->departure_routemaps, $c->departure_stationmaps ) {
			say "# $m";
		}
	}

	printf(
		"%-5s ab  %-30s %-20s %s\n",
		$c->departure_time, $c->departure_stop_and_platform,
		$c->train_line,     $c->train_destination,
	);

	if ( $opt->{'full-route'} ) {
		for my $via_stop ( $c->via ) {
			printf( "%-5s     %-30s %s\n",
				$via_stop->[1], $via_stop->[2], $via_stop->[3] );
		}
	}

	printf( "%-5s an  %s\n", $c->arrival_time, $c->arrival_stop_and_platform, );
	print "\n";

	return;
}

@ARGV = map { decode( 'UTF-8', $_ ) } @ARGV;

#<<<
GetOptions(
	$opt,
	qw{
		arrive|a=s
		auto-url|discover-and-print|A
		colorbins=i
		date|d=s
		depart=s
		discover|D
		efa-url|u=s
		endcolor=s
		endlat=f
		endlong=f
		exclude|e=s@
		extended-info|E
		from=s@{2}
		full-route|f
		gridsizelat=i
		gridsizelong=i
		help|h
		ignore-info|I:s
		include|i=s
		list|l
		maps|M
		kmlfilename=s
		max-change|m=i
		num-connections|n=i
		prefer|P=s
		proximity|p
		service|s=s
		startcolor=s
		startlat=f
		startlong=f
		time|t=s
		timeout=i
		to=s@{2}
		verbosity=i
		version|v
	},
) or show_help(1);
#>>>

if ( $opt->{list} ) {
	printf( "%-40s %-14s %s\n\n", 'service', 'abbr. (-s)', 'url (-u)' );
	for my $service ( Travel::Routing::DE::EFA::get_efa_urls() ) {
		printf( "%-40s %-14s %s\n", @{$service}{qw(name shortname url)} );
	}
	exit 0;
}



for my $pair ( [ \@from, \$from_type ], [ \@via, \$via_type ],
	[ \@to, \$to_type ], )
{

	next if ( not defined $pair->[0]->[1] );

	if (
		$pair->[0]->[1] =~ s{ ^ (?<type> [^:]+ ) : \s* (?<target> .+ ) $ }
		{$+{target}}x
	  )
	{
		given ( $+{type} ) {
			when ('addr') { ${ $pair->[1] } = 'address' }
			default       { ${ $pair->[1] } = $+{type} }
		}
	}
}

if ( defined $opt->{'ignore-info'} and length( $opt->{'ignore-info'} ) == 0 ) {
	$opt->{'ignore-info'} = undef;
}

if ( $opt->{exclude} ) {
	$opt->{exclude} = [ split( /,/, join( ',', @{ $opt->{exclude} } ) ) ];
}

if ( $opt->{service} ) {
	my $service = first { lc($_->{shortname}) eq lc($opt->{service}) }
	Travel::Routing::DE::EFA::get_efa_urls();
	if ( not $service ) {
		printf STDERR (
			"Error: Unknown service '%s'. See 'efa -l' for a "
			  . "list of supported service names\n",
			$opt->{service}
		);
		exit 1;
	}
	$efa_url = $service->{url};
}


# --- take care of gridsize
	my $gridSizeLong = 40;
	my $gridSizeLat = 60;

	if ($opt->{gridsizelong}) {
		$gridSizeLong = $opt -> {gridsizelong}
	}

	if ($opt->{gridsizelat}) {
		$gridSizeLat = $opt -> {gridsizelat}
	}

# --- take care of grid position
	my $startLat = 51.4350;
	my $endLat = 51.5130;
	my $startLong = 7.090;
	my $endLong = 7.3830;

	if ($opt->{startlat}) {
		$startLat = $opt -> {startlat};
	}

	if ($opt->{endlat}) {
		$endLat = $opt -> {endlat};
	}

	if ($opt->{startlong}) {
		$startLong = $opt -> {startlong};
	}

	if ($opt->{endlong}) {
		$endLong = $opt -> {endlong};
	}

	
# --- colors
	$startcolor = "A00000FF";
	$endcolor ="A0FF0000";

	if ($opt -> {startcolor}) {
		$startcolor = $opt -> {startcolor};
	}
	
	if ($opt -> {endcolor}) {
		$endcolor = $opt -> {endcolor};
	}

	if (!($opt -> {colorbins})) {
		my $totalRequests = $gridSizeLat * $gridSizeLong;
		$opt -> {colorbins} = $totalRequests/2;
		if ($totalRequests/2 > 32) {
			$opt -> {colorbins} = 32;
		} 
		print ("  WARNING: No value for number of color bins is given, setting it to ", $opt -> {colorbins} ,".\n");
	}
	
	
# --- destination 
	if (! ($to[0] && $to[1])) {
		print ("  WARNING: Destination was not specified. Please use --to. Setting to default now.\n");
		$to[0] = "bochum";
		$to[1] = "ruhr universitaet";
	}
	else {
	}
	

# --- time and date.
	$opt->{timeout} = 300;
	# 			$opt->{'num-connections'} = 5;

	if (!($opt -> {date}) ) {
		print ("  WARNING: No date was specified. Please use --date. Setting to a week, i.e. to ");
		
		# get todays date
		(my $xsec, my $xmin, my $xhour, my $day, my $month, my $year, my $xwday, my $xyday, my $xisdst) = localtime(time());
		
		# add a week to it
		my $today = convertDate ($year, ++$month, $day);
		my $inaweek = $today;# + 24*60*60*7;
		
		# convert to string
		($xsec, $xmin, $xhour, my $newday, my $newmonth, my $newyear, $xwday, $xyday, $xisdst) = localtime($inaweek);
		my $newarrival = sprintf ("%s.%s.%s", $newday, ++$newmonth, 1900+$newyear);
		print ($newarrival."\n");
		
		$opt -> {date} = $newarrival;
	}

	if (!($opt -> {arrive}) ) {
		print ("  WARNING: No arrival date was specified. Please use --arrive. Setting to a 10.00h.\n");
		
		# get todays date
		$opt -> {arrive} = "10:00";
	}

	
	

	
# --- output
	$kmlfilename = "./putrama.kml";

	if ($opt -> {kmlfilename}) {
		$kmlfilename = $opt -> {kmlfilename};
	}
	

# --- sanity check
	if ($endLat == $startLat) {
		print ("  WARNING: Start and end of latitute are the same. Adding one to make sense of it.\n");
		$endLat = $startLat + 1;
	}

	if ($endLong == $startLong) {
		print ("  WARNING: Start and end of longitude are the same. Adding one to make sense of it.\n");
		$endLong = $startLong + 1;
	}

	if ($endLat <  $startLat) {
		print ("  WARNING: Switched starting latitute with end latitute.\n");
		my $tmp = $startLat;
		$startLat = $endLat;
		$endLat = $tmp;
	}
		
	if ($endLong < $startLong) {
		print ("  WARNING: Switched starting longitude with end longitude.\n");
		my $tmp = $startLong;
		$startLong = $endLong;
		$endLong = $tmp;
	}
		
		
	
# --- report command line options
	if (!($opt -> {verbosity})) {
		$opt -> {verbosity} = 50;
	}
	
	print ("  Destination is set to ", $to[0], ", ", $to[1], "\n");
	print ("  Grid start point is set to $startLat x $startLong (latitude x longitude)\n");
	print ("  Grid end point is set to $endLat x $endLong (latitude x longitude)\n");
	print ("  Date is set to ", $opt -> {date}, "\n");
	print ("  Arrival time is set to ", $opt -> {arrive}, "\n");
	print ("  Grid size is $gridSizeLat x $gridSizeLong (latitude x longitude)\n");
	print ("  Will write KML file to $kmlfilename\n");
	print ("  Colors will vary from $startcolor to $endcolor\n");
	print ("  Number of color bins is ", $opt -> {colorbins}, "\n");
	print ("  Will issue ", $gridSizeLat*$gridSizeLong , " requests\n");
	print ("  Verbosity level is ", $opt -> {verbosity}, "\n");
	print ("\n");



# --- main loop	
	my $stepLat = ($endLat - $startLat)/$gridSizeLat;
	my $stepLong = ($endLong - $startLong)/$gridSizeLong;

	my $totalRequests = $gridSizeLat * $gridSizeLong;
	my $polyCounter = 0;
	for (my $mylat = $startLat; $mylat < $endLat && $polyCounter < $totalRequests; $mylat += $stepLat)
	{
		for (my $mylong = $startLong; $mylong < $endLong && $polyCounter < $totalRequests; $mylong += $stepLong)
		{
			$polyCounter += 1;
			if ($opt -> {verbosity} > 40) {
				print ("  Request [$polyCounter/$totalRequests]\n");
			}

			if ($opt -> {verbosity} > 55) {
				print ("  Finding stop near to $mylat x $mylong..\n");
			}
			my ($haltestelle, $ort, $distance) = coord_request($efa_url, $mylong, $mylat);
			if ($opt -> {verbosity} > 55) {
				print ("  Found stop $haltestelle, $ort, with distance $distance\n");
			}
			
			# we assume that we can walk 4000 meter per hour. this is in minutes.
			my $walkingtime = $distance/4000*60;

			$from[0] = $ort;
			$from[1] = $haltestelle;
			
			# do request
			$efa = eval {
			Travel::Routing::DE::EFA->new(
				efa_url => $efa_url,

				origin      => [ @from, $from_type ],
				destination => [ @to,   $to_type ],
				via => ( @via ? [ @via, $via_type ] : undef ),

				arrival_time   => $opt->{arrive},
				departure_time => $opt->{depart} // $opt->{time},
				date           => $opt->{date},
				exclude        => $opt->{exclude},
				train_type     => $opt->{include},
				with_bike      => $opt->{bike},

				select_interchange_by => $opt->{prefer},
				use_near_stops        => $opt->{proximity},
				walk_speed            => $opt->{'walk-speed'},
				max_interchanges      => $opt->{'max-change'},
				num_results           => $opt->{'num-connections'},

				lwp_options => { timeout => $opt->{timeout} },
				);
			};

			# check if we had some error
			if (!$efa) {
				if ($opt -> {verbosity} > 10) {
					print "  ############### Error. Maybe the distance is too short?\n";
				}
				next;
			}

			# get results
			my @routes = $efa->routes;

			# for each route determine the time to the destination
			my $traveltime = 0;
			for my $i ( 0 .. $#routes ) {
				my $route = $routes[$i];
				
				if ($opt -> {verbosity} > 95) {
					print ("  Route $i takes ", $route->duration, ".\n");
				}

				my @d = split(/:/, $route -> duration);

				# add to accumulated traveltime
				$traveltime += $d[0]*60 + $d[1]*1;
				
				# add time to walk to the stop
				$traveltime += $walkingtime;
			}
			
			# compute average time
			my $avgtraveltime = round($traveltime/($#routes+1));
			
			# some (debug) output
			if ($opt -> {verbosity} > 55) {
				print "\n";
				print "  Distance to next stop: $distance meter/$walkingtime min\n";
				print "  Average travel time: $avgtraveltime min\n";
			}

			
			# -- save the routes in our array
			
			# generate entitiy first
			my $mleft = ($mylong - $stepLong/2);
			my $mright = ($mylong + $stepLong/2);
			my $mtop = ($mylat - $stepLat/2);
			my $mbottom = ($mylat + $stepLat/2);
			
			my $polygon = "(($mleft,$mtop),($mright,$mtop),($mright,$mbottom),($mleft,$mbottom),($mleft,$mtop))";
			if ($opt -> {verbosity} > 85) {
				print "  $polygon\n";
			}
			
			my $data = sprintf "%.2f",$avgtraveltime;
			my $entity = {  data => $data, polygon => $polygon};
			push ($polygonList, $entity);
		};
	}


# --- finally save the data as KML file
{
	if ($opt -> {verbosity} > 20) {
		print ("  Saving data to $kmlfilename");
	}

	if ($opt -> {colorbins} < $polyCounter) {
		$opt -> {colorbins} = $polyCounter/2;
		print ("  Too many color bins, setting it to half the data points, i.e. to ", $opt -> {colorbins});
	}
	
	open (my $fh, '>', $kmlfilename) or die "cannot write file?";
	generate_kml_file(entities => $polygonList,
							placename => "TODO",
							data_desc => "Average time to travel to destination",
							nbins => $opt -> {colorbins},
							kmlfh => $fh,
							startcolor => $startcolor,
							endcolor => $endcolor);
}

# --- need some customization :(
{
	if ($opt -> {verbosity} > 20) {
		print ("  Hacking final KML file.\n");
	}

	# replace relativeToGround
	my $tmpfilename = '/tmp/tmp.kml';
	`sed -e 's/relativeToGround/clampToGround/g' $kmlfilename > $tmpfilename`;
	`mv $tmpfilename $kmlfilename`;
	
	# replace outline
	`sed -e 's#PolyStyle>#PolyStyle><outline>0</outline>#g' $kmlfilename > $tmpfilename`;
	`mv $tmpfilename $kmlfilename`;
}

# that is all, folks
	if ($opt -> {verbosity} > 20) {
		print ("  Finished! Enjoy your map!\n");
	}

__END__

=head1 NAME

