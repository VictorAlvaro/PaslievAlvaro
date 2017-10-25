open util/boolean
open util/time
open util/sequniv


sig Calendar{
	events:  set Event

}

sig User{
	travellingPreferences: one TravelPreferences,
	calendar: one Calendar
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
	endTime: one Time,
}


sig Meeting extends Event{
	departureLocation: one Position,
	meetingLocation: one Position
}

sig Break extends Event{
	timeToRest: one Int
}{
	timeToRest>0
}



sig Position{
	latitude: one Int,
	longitude: one Int
}

fact validPosition{
	all p: Position | p.latitude >=-90 and p.latitude <= 90 and p.longitude <= 180 and p.longitude >=-180
}

fact titleIsUnique{
	all e1,e2: Event | (e1 != e2) => e1.title != e2.title
}

fact oneEventAtOneTime{
	all e1,e2: Event | gt[e1.startTime,e2.endTime] or gt[e2.startTime,e1.endTime]

}

fact atLeastOneTravelPreferenceEnabled{
	all u: User | (u.travellingPreferences.car.isTrue or u.travellingPreferences.bike.isTrue or u.travellingPreferences.car.isTrue or u.travellingPreferences.ship.isTrue or u.travellingPreferences.train.isTrue or
u.travellingPreferences.walk.isTrue or u.travellingPreferences.tram.isTrue or u.travellingPreferences.taxi.isTrue or u.travellingPreferences.train.isTrue or u.travellingPreferences.plain.isTrue)
}


pred isDataCompleted[e: Event]{
	e.title != none
	gt[e.endTime, e.startTime]

}

pred freeTimeWindow[t1,t2: Time]{
	all e: Event | gt[t1, e.endTime] or gt[e.startTime, t2]
}


pred addEvent[u,u': User, e: Event]{
	not e in u.calendar.events
	u'.calendar.events = u.calendar.events + e
	e in u'.calendar.events
	
}

pred removeEvent[u,u': User, e: Event]{
	e in u.calendar.events
	u'.calendar.events = u.calendar.events - e
	not e in u'.calendar.events
}
pred createNewEvent[e: Event, u,u': User]{
	isDataCompleted[e]
	freeTimeWindow[e.startTime, e.endTime]

	addEvent[u,u',e]

		
}

pred deleteEvent[e: Event, u,u': User]{
	removeEvent[u,u',e]
	freeTimeWindow[e.startTime, e.endTime]	
}


run createNewEvent for 6 but 8 int, exactly 5 String
run deleteEvent for 6 but 8 int, exactly 5 String
