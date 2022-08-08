package database;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Timestamp;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

import politics.Candidate;
import politics.Party;
import politics.PoliticalEntity;
import polls.Poll;
import polls.PollCategorico;
import polls.PollCategorico.VoteCategorico;
import polls.PollOrdinale;
import polls.PollOrdinale.VoteOrdinale;
import polls.PollReferendum;
import polls.PollReferendum.VoteReferendum;
import polls.Vote;
import users.Elector;
import users.User;

public class PollDAOImpl implements PollDAO {
	private static PollDAO instance = null;
	private Connection connection;
	
	private PollDAOImpl() {
		connection = DatabaseConnection.getConnection();
	}
	
	public static PollDAO getInstance() {
		if(instance == null) {
			instance = new PollDAOImpl();
		}
		return instance;
	}
	
	/**
	 * Esegue le operazioni per aggiungere il referendum p al database.
	 * @param p: un oggetto di tipo PollReferendum
	 */
	private void addReferendum(PollReferendum p) {
		Objects.requireNonNull(p);
		PreparedStatement st = null;
		try {
			st = connection.prepareStatement("INSERT INTO poll(name, type, description, startDate, endDate, quorum)  VALUES (?,?,?,?,?,?);");
			st.setString(1, p.getName());
			st.setString(2, "Referendum");
			st.setString(3, p.getDescription());
			st.setTimestamp(4, p.getStartDate());
			st.setTimestamp(5, p.getEndDate());
			st.setBoolean(6, p.getQuorum());			
			st.executeUpdate();
		} catch (SQLException exc) {
			exc.printStackTrace();
		}
	}
	
	/**
	 * Esegue le operazioni per aggiungere una votazione ordinale al database.
	 * @param p: un oggetto di tipo PollOrdinale
	 */
	private void addOrdinale(PollOrdinale p) {
		Objects.requireNonNull(p);
		PreparedStatement st = null;
		try {
			st = connection.prepareStatement("INSERT INTO poll(name, type, description, startDate, endDate, absoluteMajority)  VALUES (?,?,?,?,?,?);");
			st.setString(1, p.getName());
			st.setString(2, "Ordinale");
			st.setString(3, p.getDescription());
			st.setTimestamp(4, p.getStartDate());
			st.setTimestamp(5, p.getEndDate());
			st.setBoolean(6, p.getAbsoluteMajority());			
			st.executeUpdate();
		} catch (SQLException exc) {
			exc.printStackTrace();
		}
		
		//AGGIUNGERE I CANDIDATI
		addPolitic(p, p.getCandidates());
	}
	
	/**
	 * Esegue le operazioni per aggiungere una votazione categorica al database.
	 * @param p: un oggetto di tipo PollCategorico
	 */
	private void addCategorico(PollCategorico p) {
		Objects.requireNonNull(p);
		PreparedStatement st = null;
		try {
			st = connection.prepareStatement("INSERT INTO poll(name, type, description, startDate, endDate, absoluteMajority, withPreferences)  VALUES (?,?,?,?,?,?,?);");
			st.setString(1, p.getName());
			st.setString(2, "Categorico");
			st.setString(3, p.getDescription());
			st.setTimestamp(4, p.getStartDate());
			st.setTimestamp(5, p.getEndDate());
			st.setBoolean(6, p.getAbsoluteMajority());
			st.setBoolean(7, p.getWithPreferences());
			st.executeUpdate();
		} catch (SQLException exc) {
			exc.printStackTrace();
		}
		
		//AGGIUNGERE I CANDIDATI
		addPolitic(p, p.getAllCandidates());
	}
	
	public void addPoll(Poll p) {
		Objects.requireNonNull(p);
		if(p instanceof PollReferendum) {
			addReferendum((PollReferendum) p);
		} else if(p instanceof PollOrdinale) {
			addOrdinale((PollOrdinale) p);
		} else if(p instanceof PollCategorico) {
			addCategorico((PollCategorico) p);
		} else {
			throw new IllegalArgumentException("Tipo di votazione non supportato");
		}		
	}

	public void removePoll(Poll p) {
		Objects.requireNonNull(p);
		PreparedStatement st = null;
		//Prima rimuoviamo tutte le entità politiche associate.
		removeAllPolitic(p);
		try {
			st = connection.prepareStatement("DELETE FROM poll WHERE poll.name = BINARY ?;");
			st.setString(1, p.getName());			
			st.executeUpdate();
		} catch (SQLException e) {
			e.printStackTrace();
		}		
	}
	
	/**
	 * Rimuove dal database tutte le entità politiche associate alla votazione p.
	 * @param p: La votazione a cui ci stiamo riferendo
	 */
	private void removeAllPolitic(Poll p) {
		Objects.requireNonNull(p);
		PreparedStatement st = null;
		try {
			st = connection.prepareStatement("DELETE FROM party WHERE poll = BINARY ?;");
			st.setString(1, p.getName());			
			st.executeUpdate();
			st = connection.prepareStatement("DELETE FROM candidate WHERE poll = BINARY ?;");
			st.setString(1, p.getName());			
			st.executeUpdate();
		} catch (SQLException e) {
			e.printStackTrace();
		}		
	}

	public List<Poll> getAll() {
		List<Poll> polls = new ArrayList<Poll>();
		try {
			PreparedStatement st = null;
			st = connection.prepareStatement("SELECT * FROM poll;");
			ResultSet res = st.executeQuery();
			while (res.next()) {
				Poll p = null;
				String name = res.getString("name");
				String type = res.getString("type");
				String description = res.getString("description");
				Timestamp startDate = res.getTimestamp("startDate");
				Timestamp endDate = res.getTimestamp("endDate");
				if(type.equals("Referendum")) {
					boolean quorum = res.getBoolean("quorum");
					p = new PollReferendum(name, description, startDate, endDate, quorum);
				} else if(type.equals("Ordinale")) {
					boolean absoluteMajority = res.getBoolean("absoluteMajority");
					p = new PollOrdinale(name, description, startDate, endDate, absoluteMajority);
					((PollOrdinale) p).addCandidate(getAllPolitics(p));		//aggiunta dei candidati
				} else if(type.equals("Categorico")) {
					boolean absoluteMajority = res.getBoolean("absoluteMajority");
					boolean withPreferences = res.getBoolean("withPreferences");
					p = new PollCategorico(name, description, startDate, endDate, absoluteMajority, withPreferences);
					((PollCategorico) p).addCandidate(getAllPolitics(p));	//aggiunta dei candidati
				} else {
					throw new IllegalArgumentException("Tipo non supportato: " + type);
				}
				polls.add(p);
			}
		} catch (SQLException se) {
			se.printStackTrace();
		}		
		return polls;
	}

	public Poll getPoll(String name) {
		List<Poll> polls = getAll();
		for(Poll p : polls) {
			if(p.getName().equals(name)) return p;
		}
		return null;
	}
	
	/**
	 * Restituisce true se e' gia' stato registrato almeno un voto per l'entita' politica e
	 * relativamente alla votazione p.
	 * @param p: la votazione che stiamo considerando
	 * @param e: l'entita' politica che stiamo considerando
	 * @return True quando e' gia' presente, False altrimenti
	 */
	private boolean containsPolitic(Poll p, PoliticalEntity e) {
		Objects.requireNonNull(p);
		Objects.requireNonNull(e);
		PreparedStatement st = null;
		try {
			st = connection.prepareStatement("SELECT * FROM vote WHERE vote.poll = BINARY ?"
					+ " AND vote.party = BINARY ? AND vote.name = BINARY ? AND vote.surname = BINARY ?;");
			st.setString(1, p.getName());
			if(e instanceof Party) {
				Party party = (Party) e;
				st.setString(2, party.getName());
				st.setString(3, "");
				st.setString(4, "");
			} else if(e instanceof Candidate) {
				Candidate candidate = (Candidate) e;
				st.setString(2, candidate.getParty().getName());
				st.setString(3, candidate.getName());
				st.setString(4, candidate.getSurname());
			} else {
				throw new IllegalArgumentException("Tipo di entit� politica non supportata.");
			}
			ResultSet res = st.executeQuery();
			if(res.next()) return true;
		}catch(SQLException se) {
			se.printStackTrace();
		}		
		return false;
	}
	
	/**
	 * Esegue le operazioni necessarie a registrare il voto per il referendum p.
	 * @param p: la votazione a cui ci stiamo riferendo
	 * @param v: il voto da registrare
	 */
	private void sendVoteReferendum(Poll p, VoteReferendum v) {
		Objects.requireNonNull(p);
		Objects.requireNonNull(v);
		PreparedStatement st = null;
		try {
			if(!containsPolitic(p, v.getPreference().get(0))) {
				st = connection.prepareStatement("INSERT INTO vote(poll, party, count)  VALUES (?,?,?);");
				st.setString(1, p.getName());
				String preference = ((Party) v.getPreference().get(0)).getName();
				st.setString(2, preference);
				st.setInt(3, 1);
				st.executeUpdate();
			} else {
				st = connection.prepareStatement("UPDATE vote SET count = count+1"
						+ " WHERE poll= BINARY ? AND party = BINARY ? AND name = BINARY ? AND surname = BINARY ?;");
				st.setString(1, p.getName());
				Party preference = (Party) v.getPreference().get(0);
				st.setString(2, preference.getName());
				st.setString(3, "");
				st.setString(4, "");
				st.executeUpdate();
			}
		} catch(SQLException se) {
			se.printStackTrace();
		}
	}
	
	/**
	 * Esegue le operazioni necessarie a registrare il voto per la votazione ordinale p.
	 * @param p: la votazione a cui ci stiamo riferendo
	 * @param v: il voto da registrare
	 */
	private void sendVoteOrdinale(Poll p, VoteOrdinale v) {
		Objects.requireNonNull(p);
		Objects.requireNonNull(v);
		PreparedStatement st = null;
		//Operazione da ripetere per ogni candidato segnato nella scheda
		for(int i=0 ; i < v.getPreference().size() ; i++) {
			try {
				String party = "";
				String name = "";
				String surname = "";
				PoliticalEntity e = v.getPreference().get(i);
				if(e instanceof Party) {
					party = ((Party) e).getName();
				} else if(e instanceof Candidate) {
					Candidate c = (Candidate) e;
					party = c.getParty().getName();
					name = c.getName();
					surname = c.getSurname();
				} else {
					throw new IllegalArgumentException("Tipo di candidato non supportato.");
				}
				if(!containsPolitic(p, v.getPreference().get(0))) {
					st = connection.prepareStatement("INSERT INTO vote(poll, party, name, surname, ranking, count)  VALUES (?,?,?,?,?,?);");
					st.setString(1, p.getName());					
					st.setString(2, party);
					st.setString(3, name);
					st.setString(4, surname);
					st.setInt(5, i);	//La posizione del candidato nella lista
					st.setInt(6, 1);
					st.executeUpdate();
				} else {
					st = connection.prepareStatement("UPDATE vote SET count = count+1 "
							+ "WHERE poll= BINARY ? AND party = BINARY ? AND name = BINARY ? AND surname = BINARY ? AND ranking = ?;");
					st.setString(1, p.getName());					
					st.setString(2, party);
					st.setString(3, name);
					st.setString(4, surname);
					st.setInt(5, i+1);
					st.executeUpdate();
				}
			} catch(SQLException se) {
				se.printStackTrace();
			}
		}
	}
	
	/**
	 * Esegue le operazioni necessarie a registrare il voto per la votazione categorica p.
	 * @param p: la votazione a cui ci stiamo riferendo
	 * @param v: il voto da registrare
	 */
	private void sendVoteCategorico(Poll p, VoteCategorico v) {
		Objects.requireNonNull(p);
		Objects.requireNonNull(v);
		PreparedStatement st = null;
		//Operazione da ripetere per ogni candidato segnato nella scheda
		for(int i=0 ; i < v.getPreference().size() ; i++) {
			try {
				String party = "";
				String name = "";
				String surname = "";
				PoliticalEntity e = v.getPreference().get(i);
				if(e instanceof Party) {
					party = ((Party) e).getName();
				} else if(e instanceof Candidate) {
					Candidate c = (Candidate) e;
					party = c.getParty().getName();
					name = c.getName();
					surname = c.getSurname();
				} else {
					throw new IllegalArgumentException("Tipo di candidato non supportato.");
				}
				if(!containsPolitic(p, v.getPreference().get(0))) {
					st = connection.prepareStatement("INSERT INTO vote(poll, party, name, surname, ranking, count)  VALUES (?,?,?,?,?,?);");
					st.setString(1, p.getName());					
					st.setString(2, party);
					st.setString(3, name);
					st.setString(4, surname);
					st.setInt(5, 0);
					st.setInt(6, 1);
					st.executeUpdate();
				} else {
					st = connection.prepareStatement("UPDATE vote SET count = count+1"
							+ " WHERE poll= BINARY ? AND party = BINARY ? AND name = BINARY ? AND surname = BINARY ? AND ranking = ?;");
					st.setString(1, p.getName());					
					st.setString(2, party);
					st.setString(3, name);
					st.setString(4, surname);
					st.setInt(5, 0);
					st.executeUpdate();
				}
			} catch(SQLException se) {
				se.printStackTrace();
			}
		}
	}
	
	/**
	 * Registra l'associazione tra la votazione p e lo user u se questa non e' gia'
	 * presente e restituisce True, altrimenti restituisce False.
	 * @param p: la votazione a cui ci stiamo riferendo
	 * @param u: l'utente che ha votato
	 * @return True se non era gia' presente l'associazione, False altrimenti
	 */
	private boolean registerUserVote(Poll p, User u) {
		Objects.requireNonNull(p);
		Objects.requireNonNull(u);
		PreparedStatement st = null;
		try {
			st = connection.prepareStatement("INSERT INTO vote_register(poll, user) VALUES(?,?);");
			st.setString(1, p.getName());
			st.setString(2, u.getUsername());
			st.executeUpdate();
		} catch(SQLException se) {
			//se.printStackTrace();
			return false;
		}
		return true;
	}
	
	public void sendVote(Poll p, User u, Vote v) {
		Objects.requireNonNull(p);
		Objects.requireNonNull(v);
		if(!registerUserVote(p, u)) {
			throw new IllegalArgumentException("Questo utente ha gia' votato");
		}
		if((p instanceof PollReferendum) && (v instanceof VoteReferendum)) {
			sendVoteReferendum(p, (VoteReferendum) v);
		} else if((p instanceof PollOrdinale) && (v instanceof VoteOrdinale)) {
			sendVoteOrdinale(p, (VoteOrdinale) v);
		} else if((p instanceof PollCategorico) && (v instanceof VoteCategorico)) {
			sendVoteCategorico(p, (VoteCategorico) v);
		} else {
			throw new IllegalArgumentException("Tipo non supportato o type mismatch tra votazione e voto.");
		}		
	}
	
	public List<Party> getAllParties(Poll p){
		Objects.requireNonNull(p);
		List<Party> parties = new ArrayList<Party>();
		try {
			PreparedStatement st = null;
			st = connection.prepareStatement("SELECT * FROM party WHERE party = BINARY ?;");
			st.setString(1, p.getName());
			ResultSet res = st.executeQuery();
			while (res.next()) {
				String name = res.getString("party");
				Party party = new Party(name);
				parties.add(party);			}
		} catch (SQLException se) {
			se.printStackTrace();
		}
		//if(parties.size() == 0) throw new IllegalArgumentException("Nessun partito trovato per la votazione: " + p);
		return parties;
	}
	
	public List<Candidate> getAllCandidates(Poll p){
		Objects.requireNonNull(p);
		List<Candidate> candidates = new ArrayList<Candidate>();
		try {
			PreparedStatement st = null;
			st = connection.prepareStatement("SELECT * FROM candidate WHERE candidate.poll = BINARY ?;");
			st.setString(1, p.getName());
			ResultSet res = st.executeQuery();
			while (res.next()) {
				String name = res.getString("name");
				String surname = res.getString("surname");
				Party party = new Party(res.getString("party"));
				Candidate c = new Candidate(name, surname, party);
				candidates.add(c);			}
		} catch (SQLException se) {
			se.printStackTrace();
		}
		return candidates;
	}
	
	public List<PoliticalEntity> getAllPolitics(Poll p){
		Objects.requireNonNull(p);
		List<PoliticalEntity> politics = new ArrayList<PoliticalEntity>();
		politics.addAll(getAllParties(p));
		politics.addAll(getAllCandidates(p));
		return politics;
	}
	
	/**
	 * Esegue le operazioni necessarie ad aggiungere al database un partito candidato
	 * per una votazione.
	 * @param p: la votazione a cui ci stiamo riferendo
	 * @param e: il partito da aggiungere
	 */
	private void addParty(Poll p, Party e) {
		Objects.requireNonNull(p);
		Objects.requireNonNull(e);
		PreparedStatement st = null;
		try {
			st = connection.prepareStatement("INSERT INTO party(poll, party) VALUES (?,?);");
			st.setString(1, p.getName());
			st.setString(2, e.getName());
			st.executeUpdate();
		} catch (SQLException exc) {
			exc.printStackTrace();
		}	
	}
	
	/**
	 * Esegue le operazioni necessarie ad aggiungere al database un candidato
	 * per una votazione.
	 * @param p: la votazione a cui ci stiamo riferendo
	 * @param e: il candidato da aggiungere
	 */
	private void addCandidate(Poll p, Candidate e) {
		Objects.requireNonNull(p);
		Objects.requireNonNull(e);
		PreparedStatement st = null;
		try {
			st = connection.prepareStatement("INSERT INTO candidate(poll, name, surname, party) VALUES (?,?,?,?);");
			st.setString(1, p.getName());
			st.setString(2, e.getName());
			st.setString(3, e.getSurname());
			st.setString(4, e.getParty().getName());
			st.executeUpdate();
		} catch (SQLException exc) {
			exc.printStackTrace();
		}	
	}
	
	public void addPolitic(Poll p, PoliticalEntity e) {
		Objects.requireNonNull(p);
		Objects.requireNonNull(e);
		if(e instanceof Party) {
			addParty(p, (Party) e);
		} else if(e instanceof Candidate) {
			addCandidate(p, (Candidate) e);
		} else {
			throw new IllegalArgumentException("Tipo di entita' politica non supportato.");
		}
	}
	
	public void addPolitic(Poll p, List<PoliticalEntity> e) {
		Objects.requireNonNull(p);
		Objects.requireNonNull(e);
		for(PoliticalEntity c : e) {
			addPolitic(p, c);
		}
	}
	
	public String getResults(Poll p){
		Objects.requireNonNull(p);
		String str = "";
		int total = 0;
		PreparedStatement st = null;
		ResultSet res = null;
		try {
			st = connection.prepareStatement("SELECT * FROM vote WHERE poll= BINARY ?;");
			st.setString(1, p.getName());
			res = st.executeQuery();
			while(res.next()) {
				String party = res.getString("party");
				String name = res.getString("name");
				String surname = res.getString("surname");
				int ranking = res.getInt("ranking");
				int count = res.getInt("count");
				str += party + " | " + name + " " + surname + " | posizione: " + ranking + " | n°voti: " + count + "\n";
				total += count;
			}
			str += "Voti totali: " + total;
			str += "\nNumero di votanti: " + countVoters(p);
		} catch(SQLException se) {
			se.printStackTrace();
		}		
		return str;
	}
	
	private int countVoters(Poll p) {
		Objects.requireNonNull(p);
		try {
			PreparedStatement st = null;
			st = connection.prepareStatement("SELECT COUNT(*) FROM vote_register WHERE poll = BINARY ?;");
			st.setString(1, p.getName());
			ResultSet res = st.executeQuery();
			while(res.next()) {
				return res.getInt(1);
			}
		} catch (SQLException se) {
			se.printStackTrace();
		}
		return 0;
	}
	
	@Override
	public boolean checkAvailability(Poll p, Elector e) {
		Objects.requireNonNull(p);
		Objects.requireNonNull(e);
		PreparedStatement st = null;
		ResultSet res = null;
		try {
			st = connection.prepareStatement("SELECT * FROM vote_register WHERE poll = BINARY ? AND user = BINARY ?;");
			st.setString(1, p.getName());
			st.setString(2, e.getUsername());
			res = st.executeQuery();
			if(res.next()) {
				return false;
			}else{
				return true;
			}
		} catch(SQLException se) {
			se.printStackTrace();
		}
		return true;
	}
}
