package system;

public interface SystemEvoteObservable {
	
	/**
	 * Aggiunge guiController alla lista di classi che sono iscritte
	 * agli aggiornamenti di this.
	 */
	public void addObserver(SystemEvoteObserver guiController);
	
	/**
	 * Rimuove guiController dalla lista di classi iscritte agli aggiornamenti
	 * di this.
	 */
	public void removeObserver(SystemEvoteObserver guiController);
	
	/**
	 * Informa tutti gli iscritti dei cambiamenti avvenuti.
	 */
	public void informSubscribers();
		
}
