/**
 * Le istanze di questa classe rappresentano una riga della tabella della schermata "PollSelection.fxml".
 * Conserva un riferimento all'oggetto Votazione dal quale viene creato, rende gli attributi di questo rappresentabili in forma tabellare
 * ed aggiunge i due tasti "info" e "prenota o vota" necessari rispettivamente a visualizzare i dettagli della votazione o a prenotarsi/votare
 * per essa.
 */
package gui;

import java.io.IOException;
import java.sql.Timestamp;
import java.time.Instant;
import java.util.Objects;

import javafx.beans.property.SimpleStringProperty;
import javafx.fxml.FXMLLoader;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.ButtonBar;
import javafx.scene.image.Image;
import javafx.scene.image.ImageView;
import javafx.stage.Stage;
import polls.Poll;
import polls.PollCategorico;
import polls.PollOrdinale;
import polls.PollReferendum;
import system.SystemEvote;
import users.Administrator;
import users.Elector;

public class RowPoll implements Comparable<RowPoll> {
	private final Poll p;
	private final SimpleStringProperty name;
	private final SimpleStringProperty type;
	private final SimpleStringProperty startDate;
	private final SimpleStringProperty endDate;
	private final SimpleStringProperty description;
	private final SimpleStringProperty status;
	private ButtonBar buttonBar;
	
	public RowPoll(Poll p) {
		this.p = Objects.requireNonNull(p);
		this.name = new SimpleStringProperty(p.getName());
		this.startDate = new SimpleStringProperty(p.getStartDate().toString());
		this.endDate = new SimpleStringProperty(p.getEndDate().toString());
		this.description = new SimpleStringProperty(p.getDescription());
		if(p instanceof PollReferendum) {
			this.type = new SimpleStringProperty("Referendum");
		} else if(p instanceof PollOrdinale) {
			this.type = new SimpleStringProperty("Votazione Ordinale");
		} else if(p instanceof PollCategorico) {
			this.type = new SimpleStringProperty("Votazione Categorica");
		} else {
			throw new IllegalArgumentException("Tipo non supportato.");
		}
		
		Timestamp now = Timestamp.from(Instant.now());
		if(now.before(p.getStartDate())) {
			this.status = new SimpleStringProperty("In preparazione");
		} else if(now.after(p.getEndDate())) {
			this.status = new SimpleStringProperty("Terminata");
		} else {
			this.status = new SimpleStringProperty("In corso");
		}
		
		Button button_info = new Button();
		ImageView infoPng = new ImageView(new Image(getClass().getResource("info.png").toString()));
		infoPng.setFitHeight(20);
		infoPng.setPreserveRatio(true);
		button_info.setGraphic(infoPng);
		button_info.setOnAction(event -> showMessageWindow());
		
		Button button_vota = new Button();
		ImageView votaPng = new ImageView(new Image(getClass().getResource("vote.png").toString()));
		votaPng.setFitHeight(20);
		votaPng.setPreserveRatio(true);
		button_vota.setGraphic(votaPng);
		button_vota.setOnAction(event -> handleAzioneVota());
		
		Button button_results = new Button();
		ImageView resultsPng = new ImageView(new Image(getClass().getResource("results.png").toString()));
		resultsPng.setFitHeight(20);
		resultsPng.setPreserveRatio(true);
		button_results.setGraphic(resultsPng);
		button_results.setOnAction(event -> handleGetResults());
		
		Button button_elimina = new Button();
		ImageView eliminaPng = new ImageView(new Image(getClass().getResource("delete.png").toString()));
		eliminaPng.setFitHeight(20);
		eliminaPng.setPreserveRatio(true);
		button_elimina.setGraphic(eliminaPng);
		button_elimina.setOnAction(event -> handleAzioneElimina());
		
		buttonBar = new ButtonBar();
		//buttonBar.setPadding(new Insets(0, 0, 0, 0));
		buttonBar.setButtonMinWidth(20);
		
		buttonBar.getButtons().addAll(button_info);
		buttonBar.setTranslateX(-25);


		if(SystemEvote.getInstance().getSession().getUser() instanceof Elector) {
			buttonBar.setTranslateX(-15);
			buttonBar.getButtons().addAll(button_vota);
		}else if(SystemEvote.getInstance().getSession().getUser() instanceof Administrator) {
			buttonBar.setTranslateX(-15);
			buttonBar.getButtons().addAll(button_results);
			buttonBar.getButtons().addAll(button_elimina);
		}		
	}
	
	private void handleAzioneElimina() {
		SystemEvote.getInstance().deletePoll(p);
	}
	
	public String getName() {
		return name.get();
	}
	
	public String getType() {
		return type.get();
	}
	
	public String getStartDate() {
		return startDate.get();
	}
	
	public String getEndDate() {
		return endDate.get();
	}
	
	public String getDescription() {
		return description.get();
	}
	
	public String getStatus() {
		return status.get();
	}
	
	public ButtonBar getButtonBar() {
		return buttonBar;
	}
	
	/**
	 * Alla pressione del bottone "info" viene aperta una schermata che mostra i dettagli di questa votazione.
	 */
	private void showMessageWindow() {
		try {
    		SystemEvote.getInstance().getSession().setPoll(p);
			
			Parent root = FXMLLoader.load(getClass().getResource("PollDescription.fxml"));
            Stage stage = new Stage();
        	stage.setTitle("Sistema di voto elettronico - Descrizione");
        	stage.setScene(new Scene(root, 600, 400));
        	stage.setResizable(false);
        	stage.show();
		}catch (IOException e) {
			System.out.println(e.getMessage());
		}
	}
	
	/**
	 * Alla pressione del tasto 'vota' apre la schermata per esprimere il voto.
	 */
	private void handleAzioneVota() {
		try {
			checkAvailability();
			showVoteInterface(p);
		} catch(Exception e) {
			showErrorMessage(e.getMessage());
		}
	}
	
	private void showVoteInterface(Poll poll) {
		Objects.requireNonNull(poll);
		try {
    		FXMLLoader loader = new FXMLLoader(getClass().getResource("ElectorVoteEditor.fxml"));
    		ElectorVoteEditorController controller = new ElectorVoteEditorController(poll);
    		loader.setController(controller);
    		Parent root = loader.load();
            Stage stage = new Stage();
        	stage.setTitle("Scheda elettorale");
        	stage.setScene(new Scene(root, 900, 700));
        	stage.setResizable(false);
        	stage.show();
		}catch (IOException e) {
			showErrorMessage(e.getMessage());
		}
	}
	
	private void checkAvailability() throws Exception {
		if(!SystemEvote.getInstance().checkVoteAvailability(p, (Elector)SystemEvote.getInstance().getSession().getUser())) {
			throw new Exception("Hai gia' votato per questa votazione!");
		}
		if(getStatus().equals("In preparazione")) {
			throw new Exception("La votazione non e' ancora iniziata!");
		}
		if(getStatus().equals("Terminata")) {
			throw new Exception("Troppo tardi, la votazione e' gia' finita!");
		}
	}

	@Override
	public int compareTo(RowPoll o) {
		return p.getStartDate().compareTo(o.p.getStartDate());
	}
	
	private void showErrorMessage(String s) {
		Objects.requireNonNull(s);
		String msg = "ERROR:\n\n";
		msg += s;
		try {
			FXMLLoader loader = new FXMLLoader(getClass().getResource("GeneralMessage.fxml"));
    		GeneralMessageController controller = new GeneralMessageController(msg);
    		loader.setController(controller);
    		Parent root = loader.load();
            Stage stage = new Stage();
        	stage.setTitle("ERROR");
        	stage.setScene(new Scene(root, 600, 400));
        	stage.setResizable(false);
        	stage.show();
		} catch (Exception e) {
			showErrorMessage(e.getMessage());
			e.printStackTrace();
		}
	}
	
	private void handleGetResults() {
		try {
			String results = SystemEvote.getInstance().getPollResults(p);
			FXMLLoader loader = new FXMLLoader(getClass().getResource("GeneralMessage.fxml"));
    		GeneralMessageController controller = new GeneralMessageController(results);
    		loader.setController(controller);
    		Parent root = loader.load();
            Stage stage = new Stage();
        	stage.setTitle("Risultati " + p.getName());
        	stage.setScene(new Scene(root, 600, 400));
        	stage.setResizable(false);
        	stage.show();
		} catch (Exception e) {
			showErrorMessage(e.getMessage());
			e.printStackTrace();
		}
	}
	
}
