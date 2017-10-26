open util/boolean
open util/time
open util/integer


sig Calendar{
	events:  set Event
}

sig User{
	travellingPreferences: one TravelPreferences,
	calendar: one Calendar
}

sig Route{
	duration: one Int,
	transport: one TravelPreferences,
	cheapestOption: one Bool,
	fastestOption: one Bool,
	leastCarbonEmissions: one Bool,
	emissions: one Int,
	price: one Int
}
{
	duration>0
	price>0
	emissions>0
}

sig TravelPreferences{
	car: one  Bool,
	plain: one Bool,
	train: one Bool,
	tram: one Bool,
	taxi: one Bool,
	walk: one Bool,
	bike: one Bool,
	ship: one Bool
}

abstract sig Event{
	title: one String,
	startTime: one Time,
	endTime: one Time
}

sig Meeting extends Event{
	departureLocation: one Position,
	meetingLocation: one Position,
	routes: set Route
}

sig Break extends Event{
	timeToRest: one Int
}{
	timeToRest>0
}

sig Position{
	latitude: Int,
	longitude: Int
}

--Each route has only one type of transport. It is true that they might have more but it is assumed to simplify.
fact justOneTransportRoute{
	all r: Route, u: User | r.transport.car.isTrue && u.travellingPreferences.car.isTrue => not r.transport.bike.isTrue && not r.transport.train.isTrue && not r.transport.tram.isTrue && not r.transport.plain.isTrue && not r.transport.taxi.isTrue && not r.transport.walk.isTrue && not r.transport.ship.isTrue
	all r: Route, u: User | r.transport.ship.isTrue && u.travellingPreferences.ship.isTrue=> not r.transport.bike.isTrue && not r.transport.train.isTrue && not r.transport.tram.isTrue && not r.transport.plain.isTrue && not r.transport.taxi.isTrue && not r.transport.walk.isTrue && not r.transport.car.isTrue
	all r: Route, u: User | r.transport.train.isTrue && u.travellingPreferences.train.isTrue => not r.transport.bike.isTrue && not r.transport.car.isTrue && not r.transport.tram.isTrue && not r.transport.plain.isTrue && not r.transport.taxi.isTrue && not r.transport.walk.isTrue && not r.transport.ship.isTrue
	all r: Route, u: User | r.transport.bike.isTrue && u.travellingPreferences.bike.isTrue => not r.transport.car.isTrue && not r.transport.train.isTrue && not r.transport.tram.isTrue && not r.transport.plain.isTrue && not r.transport.taxi.isTrue && not r.transport.walk.isTrue && not r.transport.ship.isTrue
	all r: Route, u: User | r.transport.plain.isTrue && u.travellingPreferences.plain.isTrue => not r.transport.bike.isTrue && not r.transport.train.isTrue && not r.transport.tram.isTrue && not r.transport.car.isTrue && not r.transport.taxi.isTrue && not r.transport.walk.isTrue && not r.transport.ship.isTrue
	all r: Route, u: User | r.transport.walk.isTrue && u.travellingPreferences.walk.isTrue => not r.transport.bike.isTrue && not r.transport.train.isTrue && not r.transport.tram.isTrue && not r.transport.plain.isTrue && not r.transport.taxi.isTrue && not r.transport.car.isTrue && not r.transport.ship.isTrue
	all r: Route, u: User | r.transport.taxi.isTrue && u.travellingPreferences.taxi.isTrue => not r.transport.bike.isTrue && not r.transport.train.isTrue && not r.transport.tram.isTrue && not r.transport.plain.isTrue && not r.transport.car.isTrue && not r.transport.walk.isTrue && not r.transport.ship.isTrue
	all r: Route, u: User | r.transport.tram.isTrue && u.travellingPreferences.tram.isTrue=> not r.transport.bike.isTrue && not r.transport.train.isTrue && not r.transport.car.isTrue && not r.transport.plain.isTrue && not r.transport.taxi.isTrue && not r.transport.walk.isTrue && not r.transport.ship.isTrue
}

--Just one option of cheapest, fastest and least carbon emissions for each set of routes.
fact oneRouteSelected{
	all r1,r2: Route | r1.duration < r2.duration =>r1.fastestOption.isTrue && not r2.fastestOption.isTrue
	all r1,r2: Route | r1.emissions < r2.emissions =>r1.leastCarbonEmissions.isTrue && not r2.leastCarbonEmissions.isTrue
	all r1,r2: Route | r1.price < r2.price =>r1.cheapestOption.isTrue && not r2.cheapestOption.isTrue
}

--Each event has his own title.
fact titleIsUnique{
	all disj e1,e2: Event | disj[e1.title,e2.title]
}

--The latitude and longitude must be inside the valid values.
fact validPosition{
	all p:Position | p.latitude<90 && p.latitude>-90 && p.longitude>-180 && p.longitude<180
}

--At any Time there must be just one event. Also the startTime and the endTime of the event must be different
fact oneEventAtOneTime{
	all disj e1,e2: Event | (gt[e1.startTime,e2.endTime] or gt[e2.startTime,e1.endTime]) 
	all disj e3,e4: Event | disj [e3.endTime, e4.endTime] and disj[e3.startTime, e4.startTime]
	all disj e: Event | disj[e.startTime, e.endTime]
}

--Each User must have his own calendar
fact unicCalendar{
	all disj u1,u2: User | disj[u1.calendar, u2.calendar]
}

--There must be at leat one travel preference enable because if not, is not possible to show any route to the user
fact atLeastOneTravelPreferenceEnabled{
	all u: User | (u.travellingPreferences.car.isTrue or u.travellingPreferences.bike.isTrue or u.travellingPreferences.car.isTrue or u.travellingPreferences.ship.isTrue or u.travellingPreferences.train.isTrue or
u.travellingPreferences.walk.isTrue or u.travellingPreferences.tram.isTrue or u.travellingPreferences.taxi.isTrue or u.travellingPreferences.train.isTrue or u.travellingPreferences.plain.isTrue)
}

--	Checks if the data of the event is not null.
pred isDataCompleted[e: Event]{
	e.title != none
	e.startTime != none
	e.endTime != none	
}

--Checks if in the interval of time t1:startTime, t2:endTime of the event there is not any events in the 
--calendar of the user.
pred freeTimeWindow[t1,t2: Time, c: Calendar]{
	all e: c.events | gt[t1, e.endTime] or gt[e.startTime, t2]
}

--Adding an event to the set of events of the calendar of the user u. After that there is created
--a new user u' with the new event included. Fist of all, checks that the event is not in the set.
--After that is added and finally checks that is inside the set after adding it.
pred addEvent[u,u': User, e: Event]{
	not e in u.calendar.events
	u'.calendar.events = u.calendar.events + e
	e in u'.calendar.events
	
}

--Removing an event to the set of events of the calendar of the user u. After that there is created
--a new user u' without the event e. Fist of all, checks that the event is in the set.
--After that is removed and finally checks that is not inside the set after removing it.
pred removeEvent[u,u': User, e: Event]{
	e in u.calendar.events
	u'.calendar.events = u.calendar.events - e
	not e in u'.calendar.events
}

--Before creating the new event, it is checked if the event has a title and also if there is a free window
--in the interval of time of the event in the calendar of the user.
pred createNewEvent[e: Event, u,u': User]{
	isDataCompleted[e]
	freeTimeWindow[e.startTime, e.endTime, u.calendar]

	addEvent[u,u',e]

}

--After removing the event, it is checked if there is a free window in the calendar of the user in the interval
--time of the event removed.
pred deleteEvent[e: Event, u,u': User]{
	removeEvent[u,u',e]
	freeTimeWindow[e.startTime, e.endTime, u'.calendar]	
}


run createNewEvent for 5 but 8 int, 2 User, 2 Calendar, exactly 2 Break, exactly 3 Meeting, exactly 3 Route, 10 Time, exactly 5 String
run deleteEvent for 6 but 8 int, exactly 5 String
