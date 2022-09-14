package gui;

import java.io.IOException;
import java.net.URL;
import java.sql.Timestamp;
import java.time.Instant;
import java.time.LocalDateTime;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.ResourceBundle;

import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.fxml.Initializable;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.CheckBox;
import javafx.scene.control.ChoiceBox;
import javafx.scene.control.DatePicker;
import javafx.scene.control.Label;
import javafx.scene.control.TextArea;
import javafx.scene.control.TextField;
import javafx.stage.Stage;
import polls.Poll;
import polls.PollCategorico;
import polls.PollOrdinale;
import polls.PollReferendum;
import system.SystemEvote;

public class AdminPollEditorController implements Initializable {

	@FXML
    private Button categoricoAddButton;

    @FXML
    private TextArea categoricoDescriptionField;

    @FXML
    private DatePicker categoricoEndDateField;

    @FXML
    private Label categoricoEndDateLabel;

    @FXML
    private ChoiceBox<Integer> categoricoEndHhChoice;

    @FXML
    private ChoiceBox<Integer> categoricoEndMmChoice;

    @FXML
    private TextField categoricoNameField;

    @FXML
    private Label categoricoNameLabel;

    @FXML
    private DatePicker categoricoStartDateField;

    @FXML
    private Label categoricoStartDateLabel;

    @FXML
    private ChoiceBox<Integer> categoricoStartHhChoice;

    @FXML
    private ChoiceBox<Integer> categoricoStartMmChoice;

    @FXML
    private Label categoricoStatusLabel;

    @FXML
    private ChoiceBox<String> categoricoTypeChoice;

    @FXML
    private Button ordinaleAddButton;

    @FXML
    private TextArea ordinaleCandidateListField;

    @FXML
    private TextArea ordinaleDescriptionField;

    @FXML
    private DatePicker ordinaleEndDateField;

    @FXML
    private Label ordinaleEndDateLabel;

    @FXML
    private ChoiceBox<Integer> ordinaleEndHhChoice;

    @FXML
    private ChoiceBox<Integer> ordinaleEndMmChoice;

    @FXML
    private TextField ordinaleNameField;

    @FXML
    private Label ordinaleNameLabel;

    @FXML
    private DatePicker ordinaleStartDateField;

    @FXML
    private Label ordinaleStartDateLabel;

    @FXML
    private ChoiceBox<Integer> ordinaleStartHhChoice;

    @FXML
    private ChoiceBox<Integer> ordinaleStartMmChoice;

    @FXML
    private Label ordinaleStatusLabel;

    @FXML
    private ChoiceBox<String> ordinaleTypeChoice;

    @FXML
    private Button referendumAddButton;

    @FXML
    private TextArea referendumDescriptionField;

    @FXML
    private DatePicker referendumEndDateField;

    @FXML
    private Label referendumEndDateLabel;

    @FXML
    private ChoiceBox<Integer> referendumEndHhChoice;

    @FXML
    private ChoiceBox<Integer> referendumEndMmChoice;

    @FXML
    private TextField referendumNameField;

    @FXML
    private Label referendumNameLabel;

    @FXML
    private DatePicker referendumStartDateField;

    @FXML
    private Label referendumStartDateLabel;

    @FXML
    private ChoiceBox<Integer> referendumStartHhChoice;

    @FXML
    private ChoiceBox<Integer> referendumStartMmChoice;

    @FXML
    private Label referendumStatusLabel;

    @FXML
    private ChoiceBox<String> referendumTypeChoice;
    
    @FXML
    private CheckBox ordinaleMaggioranzaAssoluta;
    
    @FXML
    private CheckBox categoricoMaggioranzaAssoluta;
    
    @FXML
    private CheckBox categoricoConPreferenze;

    @FXML
    void addReferendum(ActionEvent event) {
    	try {
	    	String name = referendumNameField.getText();
	    	String description = referendumDescriptionField.getText();
	    	Timestamp startDate = buildDate(referendumStartDateField, referendumStartHhChoice.getValue(), referendumStartMmChoice.getValue());
	    	Timestamp endDate = buildDate(referendumEndDateField, referendumEndHhChoice.getValue(), referendumEndMmChoice.getValue());
	    	validateDate(startDate, endDate);
	    	boolean quorum = referendumTypeChoice.getValue().equals("Con quorum");
	    	Poll p = new PollReferendum(name, description, startDate, endDate, quorum);
	    	addPoll(p);
	    	referendumAddButton.getScene().getWindow().hide();
    	} catch(NullPointerException npe) {
    		showErrorMessage("Non sono stati inseriti tutti i dati");
    	}catch(Exception e) {
    		showErrorMessage(e.getMessage());
    	}
    }
    
    @FXML
    void addOrdinale(ActionEvent event) {
    	try {
	    	String name = ordinaleNameField.getText();
	    	String description = ordinaleDescriptionField.getText();
	    	Timestamp startDate = buildDate(ordinaleStartDateField, ordinaleStartHhChoice.getValue(), ordinaleStartMmChoice.getValue());
	    	Timestamp endDate = buildDate(ordinaleEndDateField, ordinaleEndHhChoice.getValue(), ordinaleEndMmChoice.getValue());
	    	validateDate(startDate, endDate);
	    	boolean absoluteMajority = ordinaleMaggioranzaAssoluta.isArmed();
	    	Poll p = new PollOrdinale(name, description, startDate, endDate, absoluteMajority);
	    	addPoll(p);
	    	showAddCandidateWindow(p, ordinaleTypeChoice.getValue().equals("A partiti"));
	    	ordinaleAddButton.getScene().getWindow().hide();
    	} catch(NullPointerException npe) {
    		showErrorMessage("Non sono stati inseriti tutti i dati");
    	}catch(Exception e) {
    		showErrorMessage(e.getMessage());
    	}
    }

    @FXML
    void addCategorico(ActionEvent event) {
    	try {
	    	String name = categoricoNameField.getText();
	    	String description = categoricoDescriptionField.getText();
	    	Timestamp startDate = buildDate(categoricoStartDateField, categoricoStartHhChoice.getValue(), categoricoStartMmChoice.getValue());
	    	Timestamp endDate = buildDate(categoricoEndDateField, categoricoEndHhChoice.getValue(), categoricoEndMmChoice.getValue());
	    	validateDate(startDate, endDate);
	    	boolean absoluteMajority = categoricoMaggioranzaAssoluta.isArmed();
	    	boolean withPreferences = categoricoTypeChoice.getValue().equals("A partiti con preferenze");
	    	Poll p = new PollCategorico(name, description, startDate, endDate, absoluteMajority, withPreferences);
	    	addPoll(p);
	    	showAddCandidateWindow(p, categoricoTypeChoice.getValue().equals("A partiti"));
	    	categoricoAddButton.getScene().getWindow().hide();
    	}catch(NullPointerException npe) {
    		showErrorMessage("Non sono stati inseriti tutti i dati");
    	}catch(Exception e) {
    		showErrorMessage(e.getMessage());
    	}
    }
    
    private void showAddCandidateWindow(Poll p, boolean onlyParties) {
    	Objects.requireNonNull(p);
    	try {
    		FXMLLoader loader = new FXMLLoader(getClass().getResource("AdminPollAddCandidate.fxml"));
    		AdminPollAddCandidateController controller = new AdminPollAddCandidateController(p, onlyParties);
    		loader.setController(controller);
    		Parent root = loader.load();
    		//Parent root = FXMLLoader.load(getClass().getResource("AdminPollAddCandidate.fxml"));
            Stage stage = new Stage();
        	stage.setTitle("Sistema di voto elettronico - Inserimento candidati");
        	stage.setScene(new Scene(root, 500, 400));
        	stage.setResizable(false);
        	stage.show();
		}catch (IOException e) {
			System.out.println(e.getMessage());
		}
    }

	@Override
	public void initialize(URL location, ResourceBundle resources) {
		initializeTimePicker(referendumStartHhChoice, referendumStartMmChoice);
		initializeTimePicker(ordinaleStartHhChoice, ordinaleStartMmChoice);
		initializeTimePicker(categoricoStartHhChoice, categoricoStartMmChoice);
		initializeTimePicker(referendumEndHhChoice, referendumEndMmChoice);
		initializeTimePicker(ordinaleEndHhChoice, ordinaleEndMmChoice);
		initializeTimePicker(categoricoEndHhChoice, categoricoEndMmChoice);
		
		referendumTypeChoice.getItems().addAll("Senza quorum", "Con quorum");
		referendumTypeChoice.setValue("Senza quorum");
		ordinaleTypeChoice.getItems().addAll("A candidati", "A partiti");
		ordinaleTypeChoice.setValue("Votazione a candidati");
		categoricoTypeChoice.getItems().addAll("A candidati", "A partiti", "A partiti con preferenze");
		categoricoTypeChoice.setValue("A candidati");
	}
	
	/**
	 * Restituisce un oggetto di tipo timestamp che rappresenti la data
	 * selezionata nel DatePicker dp ed integrandola con le ore fornite
	 * da hh ed i minuti forniti da mm.
	 * @param dp: il datepicker in cui è stata selezionata la data
	 * @param hh: le ore
	 * @param mm: i minuti
	 * @return un'istanza di timestamp che rappresenta la data dd/mm/yy hh:mm
	 */
	private Timestamp buildDate(DatePicker dp, int hh, int mm) {
		Objects.requireNonNull(dp);
		LocalDateTime ldt = dp.getValue().atStartOfDay();
		ldt = ldt.plusHours(hh);
		ldt = ldt.plusMinutes(mm);
		return Timestamp.valueOf(ldt);		
	}
	
	/**
	 * Aggiunge al sistema la votazione p.
	 * @param p
	 */
	private void addPoll(Poll p) {
    	SystemEvote.getInstance().addPoll(p);
	}
	
	/**
	 * Se 'start' precede 'end' e sono entrambe date successive rispetto a now non fa nulla.
	 * Altrimenti lancia una IllegalArgumentException
	 * @param start: la data di inizio
	 * @param end: la data di fine
	 * @throws IllegalArgumentException
	 */
	private void validateDate(Timestamp start, Timestamp end) throws IllegalArgumentException {
		Timestamp now = Timestamp.from(Instant.now());
		if(start.after(end) || now.after(start)) {
			throw new IllegalArgumentException("Date non valide.");
		}
	}
	
	/**
	 * Inizializza i valori messi a disposizione dai TimePicker affinchè fungano da selezione di un orario.
	 * @param boxHh Il ChoiceBox che deve servire a selezionare l'ora
	 * @param boxMm Il ChoiceBox che deve servire a selezionare il minuto
	 */
	private void initializeTimePicker(ChoiceBox<Integer> boxHh, ChoiceBox<Integer> boxMm) {
		List<Integer> ore = new ArrayList<>();
		for(int i=0 ; i <= 23 ; i++) {
			ore.add(i);
		}
		List<Integer> minuti = new ArrayList<>();
		for(int i=0 ; i <= 59 ; i++) {
			minuti.add(i);
		}
		boxHh.getItems().addAll(ore);
		boxMm.getItems().addAll(minuti);
		boxHh.setValue(0);
		boxMm.setValue(0);
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
}

