package system;

import java.sql.Timestamp;
import java.time.Instant;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

import database.PollDAOImpl;
import database.UserDAOImpl;
import polls.Poll;
import polls.Vote;
import users.Administrator;
import users.Elector;
import users.User;

public class SystemEvote implements SystemEvoteObservable {
	
	private static SystemEvote system = null;
	private final Timestamp timestamp;
	private Session session;
	private List<User> users;
	private List<Poll> polls;
	private List<String> logs;
	private List<SystemEvoteObserver> subscribers;
	
	private SystemEvote() {
		timestamp = Timestamp.from(Instant.now());
		session = null;
		users = new ArrayList<User>();
		polls = new ArrayList<Poll>();
		subscribers = new ArrayList<SystemEvoteObserver>();
		refresh();
	}
	
	public static SystemEvote getInstance() {
		if(system == null) {
			system = new SystemEvote();
		}
		return system;
	}
	
	public Session getSession() {
		return session;
	}
	
	public List<User> getUsers() {
		return users;
	}
	
	public List<Poll> getPolls() {
		return polls;
	}
	
	public void addUser(User u, String password) throws IllegalArgumentException {
		Objects.requireNonNull(u);
		Objects.requireNonNull(password);
		for(User i : users) {
			if(i.equals(u)) {
				throw new IllegalArgumentException("Utente gia' presente nel sistema");
			}
			if(i.getUsername().equals(u.getUsername())) {
				throw new IllegalArgumentException("Username gia' in uso: " + i.getUsername());
			}
		}
		UserDAOImpl.getInstance().addUser(u, password);
		UserDAOImpl.getInstance().addLogEntry((Administrator) session.getUser(), "AGGIUNGE UTENTE",u);
		refresh();
	}
	
	public void deleteUser(User u) {
		Objects.requireNonNull(u);
		if(u.equals(session.getUser())) {
			throw new IllegalArgumentException("Non è possibile eliminare l'account se questo è in uso.");
		}
		UserDAOImpl.getInstance().deleteUser(u);
		UserDAOImpl.getInstance().addLogEntry((Administrator) session.getUser(), "ELIMINA UTENTE",u);
		refresh();
	}
	
	public void addPoll(Poll p) throws IllegalArgumentException {
		Objects.requireNonNull(p);
		for(Poll i : polls) {
			if(i.equals(p)) {
				throw new IllegalArgumentException("Votazione gia' presente nel sistema");
			}
			if(i.getName().equals(p.getName())) {
				throw new IllegalArgumentException("Nome già in uso: " + i.getName());
			}
		}
		if(!Timestamp.from(Instant.now()).before(p.getStartDate())) {
			throw new IllegalArgumentException("La data di inizio votazione deve essere successiva a quella attuale.");
		}
		PollDAOImpl.getInstance().addPoll(p);
		UserDAOImpl.getInstance().addLogEntry(session.getUser(), "CREA VOTAZIONE",p);
		refresh();
	}
	
	public void deletePoll(Poll p) {
		if(!polls.contains(p)) {
			throw new IllegalArgumentException("Votazione non presente nel sistema.");
		}
		if(Timestamp.from(Instant.now()).after(p.getStartDate())) {
			throw new IllegalArgumentException("Non è possibile eliminare una votazione dopo la sua data di inizio.");
		}
		PollDAOImpl.getInstance().removePoll(p);
		UserDAOImpl.getInstance().addLogEntry(session.getUser(), "ELIMINA VOTAZIONE",p);
		refresh();
	}
	
	public void sendVote(Poll p, Vote v) {
		Objects.requireNonNull(p);
		Objects.requireNonNull(v);
		PollDAOImpl.getInstance().sendVote(p, session.getUser(), v);
		UserDAOImpl.getInstance().addLogEntry(session.getUser(), "VOTA",p);
	}
	
	/**
	 * Metodo che permette di istanziare una sessione per il sistema dato un utente.
	 * @param user: Un oggetto di tipo user che rappresenta un utente del sistema.
	 */
	private void startSession(User user) {
		Objects.requireNonNull(user);
		if(user instanceof Elector) {
			Elector e = (Elector) user;
			session = new SessionElector(e);
		}else if(user instanceof Administrator) {
			Administrator a = (Administrator) user;
			session = new SessionAdministrator(a);
		}
		refresh();
	}
	
	/**
	 * Istanzia una sessione per l'utente del sistema definito da username+password.
	 * @param username: lo username dell'utente
	 * @param password: la password dell'utente
	 */
	public void login(String username, String password) {
		Objects.requireNonNull(username);
		Objects.requireNonNull(password);
		User u = UserDAOImpl.getInstance().login(username, password);
		startSession(u);
		UserDAOImpl.getInstance().addLogEntry(u, "LOGIN");
		refresh();
	}	
	
	/**
	 * Esegue il logout eliminando la sessione attualmente attiva.
	 */
	public void logout() {
		UserDAOImpl.getInstance().addLogEntry(session.getUser(), "LOGOUT");
		session = null;
		refresh();
	}
	
	/**
	 * Restituisce la lista degli utenti scaricata dal database.
	 */
	private List<User> downloadUsers() {
		System.out.println("Downloading users...");
		return UserDAOImpl.getInstance().getAll();
	}
	
	/**
	 * Restituisce la lista delle votazioni scaricata dal database
	 */
	private List<Poll> downloadPolls() {
		System.out.println("Downloading polls...");
		return PollDAOImpl.getInstance().getAll();
	}
	
	private List<String> downloadLogs(){
		System.out.println("Downloading logs...");
		return UserDAOImpl.getInstance().getLog();
	}
	
	/**
	 * Aggiorna le informazioni locali relative ad utenti e votazioni sincronizzandole
	 * con quelle contenute nel database.
	 */
	public void refresh() {
		users = downloadUsers();
		polls = downloadPolls();
		logs = downloadLogs();
		informSubscribers();
	}
	
	@Override
	public String toString() {
		return "Sistema di voto avviato il " + timestamp;
	}

	public void addObserver(SystemEvoteObserver guiController) {
		Objects.requireNonNull(guiController);
		if(subscribers.contains(guiController))
			return;
		subscribers.add(guiController);
		System.out.println("Added 1 observer. Observers: " + subscribers.size());
		informSubscribers(guiController);
	}

	public void removeObserver(SystemEvoteObserver guiController) {
		if(!subscribers.contains(guiController))
			return;
		subscribers.remove(guiController);	
		System.out.println("Removed 1 observer. Observers: " + subscribers.size());
	}
	
	public void informSubscribers() {
		System.out.println("Informing subscribers...");
		for(SystemEvoteObserver s : subscribers) {
			if(s != null)
				s.update(users, polls,logs);
		}
	}
	
	public void informSubscribers(SystemEvoteObserver o) {
		Objects.requireNonNull(o);
		if(subscribers.contains(o)) {
			System.out.println("Informing a subscriber...");
			o.update(users, polls,logs);
		} else {
			throw new IllegalArgumentException("L'observer non risulta iscritto: " + o);
		}
	}
	
	public boolean checkVoteAvailability(Poll p, Elector e) {
		Objects.requireNonNull(p);
		Objects.requireNonNull(e);
		return PollDAOImpl.getInstance().checkAvailability(p, e);
	}
	
	public String getPollResults(Poll p) throws Exception {
		Objects.requireNonNull(p);
		if(Timestamp.from(Instant.now()).before(p.getEndDate())) {
			throw new IllegalArgumentException("I risultati possono essere consultati solo al termine della votazione.");
		}
		return PollDAOImpl.getInstance().getResults(p);
	}
	
}
