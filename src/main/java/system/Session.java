package system;

import java.sql.Timestamp;
import java.time.Instant;
import java.util.Objects;

import polls.Poll;
import users.User;

public abstract class Session {
	private final Timestamp timestamp;
	private final User user;
	private Poll poll;
	
	public Session(User user) {
		this.timestamp = Timestamp.from(Instant.now());
		this.user = Objects.requireNonNull(user);
	}
	
	public User getUser() {
		return user;
	}
	
	public Poll getPoll() {
		return poll;
	}
	
	public void setPoll(Poll p) {
		poll = Objects.requireNonNull(p);
	}
	
	@Override
	public boolean equals(Object o) {
		if(o instanceof Session) {
			Session s = (Session) o;
			return user.equals(s.user) && timestamp.equals(s.timestamp);
		}
		return false;
	}
	
	@Override
	public String toString() {
		return "Sessione iniziata dall'utente " + user + " il " + timestamp;
	}
}
