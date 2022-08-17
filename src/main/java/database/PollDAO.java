package database;

import java.util.List;

import politics.PoliticalEntity;
import polls.Poll;
import polls.Vote;
import users.Elector;
import users.User;

public interface PollDAO {
	
	/**
	 * Registra la votazione p nel database.
	 * @param p: l'oggetto Poll che rappresenta la votazione da aggiungere al database
	 */
	public void addPoll(Poll p);
	
	/**
	 * Rimuove la votazione p dal database.
	 * @param p: l'oggetto Poll che rappresenta la votazione da eliminare dal database
	 */
	public void removePoll(Poll p);
	
	/**
	 * Restituisce una lista contenente tutte le votazioni registrate nel sistema
	 * @return Una lista di oggetti Poll che rappresentano tutte le votazioni registrate nel sistema
	 */
	public List<Poll> getAll();
	
	/**
	 * Restituisce la votazione identificata da 'name'.
	 * @param name: il nome della votazione che si vuole cercare nel database.
	 * @return L'oggetto Poll che rappresenta la votazione identificata da 'name'
	 */
	public Poll getPoll(String name);
	
	/**
	 * Registra nel database i voti aggiunti alla votazione p e registra che lo user u
	 * ha votato per la votazione p.
	 * @param p: un oggetto di tipo Poll
	 * @param u: l'utente che ha prodotto il voto
	 * @param v: il voto da registrare
	 */
	public void sendVote(Poll p, User u, Vote v);
	
	/**
	 * Restituisce una lista di tutte le entita politiche candidate per la votazione p.
	 * @param p: l'istanza di Poll di cui si vuole ottenere i candidati
	 * @return Una lista di PoliticalEntity che rappresentano tutti i candidati della votazione p.
	 */
	public List<PoliticalEntity> getAllPolitics(Poll p);
	
	/**
	 * Aggiunge al database l'entit� politica e associata alla votazione p.
	 * @param p: la votazione a cui ci stiamo riferendo
	 * @param e: l'entit� politica da aggiungere
	 */
	public void addPolitic(Poll p, PoliticalEntity e);
	
	/**
	 * Aggiunge al database la lista di entit� politiche e associate ad una votazione p.
	 * @param p: la votazione a cui ci stiamo riferendo
	 * @param e: la lista di entit� politiche da aggiungere
	 */
	public void addPolitic(Poll p, List<PoliticalEntity> e);
	
	/**
	 * Restituisce una stringa che rappresenta i risultati della votazione p.
	 * Viene elencato ogni candidato con il numero di voti e la percentuale rispetto al totale.
	 * @param p: la votazione a cui ci stiamo riferendo.
	 * @return
	 */
	public String getResults(Poll p);
	
	/**
	 * Restituisce True se l'elettore e non ha ancora votato per la votazione p.
	 * @param p: la votazione a cui ci stiamo riferendo
	 * @param e: l'elettore
	 * @return True se e non ha ancora votato per p, false altrimenti.
	 */
	public boolean checkAvailability(Poll p, Elector e);
}
