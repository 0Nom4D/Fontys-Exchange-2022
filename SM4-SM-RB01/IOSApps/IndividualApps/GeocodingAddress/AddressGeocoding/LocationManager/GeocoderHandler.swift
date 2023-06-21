//
//  GeocoderHandler.swift
//  AddressGeocoding
//
//  Created by Nom4D on 20/03/2023.
//

import Foundation
import CoreLocation
import Combine
import MapKit

class GeocoderHandler: NSObject, ObservableObject, MKLocalSearchCompleterDelegate {
    // Variables
    @Published private var _currentLocation: Location = Location(name: "", additionalName: "", description: "", coordinates: nil)
    @Published private var _lastFetchedLocations: [MKLocalSearchCompletion] = []
    @Published private var _knownLocations: Set<Location> = []

    @Published private var _sendLocationRequest: Bool = false
    @Published private var _isDetailed: Bool = false
    @Published var request = ""

    private var currentPromise : ((Result<[MKLocalSearchCompletion], Error>) -> Void)?
    private var searchCompleter: MKLocalSearchCompleter = MKLocalSearchCompleter()
    private var cancellables: Set<AnyCancellable> = []

    private var geocoderHandler = CLGeocoder()

    private var observers = [NSObjectProtocol]()

    // Getters & Setters
    var currentLocation: Location {
        get { return self._currentLocation }
        set { self._currentLocation = newValue }
    }
    
    var isDetailed: Bool {
        get { return self._isDetailed }
        set { self._isDetailed = newValue }
    }

    var sendLocationRequest: Bool {
        get { return self._sendLocationRequest }
        set { self._sendLocationRequest = newValue }
    }

    var knownLocations: Set<Location> {
        get { return self._knownLocations }
        set { self._knownLocations = newValue }
    }

    var lastFetchedLocations: [MKLocalSearchCompletion] {
        get { return self._lastFetchedLocations }
    }

    // Constructors - Destructors
    override init() {
        super.init()

        observers.append(
            NotificationCenter.default.addObserver(forName: UIApplication.willTerminateNotification, object: nil, queue: .main) { _ in
                self.storeLocalStorage()
            }
        )

        searchCompleter.delegate = self
        searchCompleter.resultTypes = MKLocalSearchCompleter.ResultType([.query])
        $request
            .debounce(for: .seconds(0.5), scheduler: RunLoop.main)
            .removeDuplicates()
            .flatMap({ (currentSearchTerm) in self.searchTermToResults(searchTerm: currentSearchTerm) })
            .sink(receiveCompletion: { (completion) in print(completion) }, receiveValue: { (results) in self._lastFetchedLocations = results })
            .store(in: &cancellables)
    }

    deinit {
        observers.forEach(NotificationCenter.default.removeObserver)
    }

    // Methods
    func searchTermToResults(searchTerm: String) -> Future<[MKLocalSearchCompletion], Error> {
        Future { promise in
            self.searchCompleter.queryFragment = searchTerm
            self.currentPromise = promise
        }
    }

    func completerDidUpdateResults(_ completer: MKLocalSearchCompleter) {
        self._lastFetchedLocations = completer.results
    }
    
    func completer(_ completer: MKLocalSearchCompleter, didFailWithError error: Error) {
        print(error.localizedDescription)
    }

    func getSearchedLocationsNames() -> [Location] {
        return self.lastFetchedLocations.compactMap({ location in
            return Location(name: location.title, additionalName: location.subtitle, description: location.description, coordinates: nil)
        })
    }

    func findLocation(location: Location) {
        if location.coordinates != nil {
            self.currentLocation = location
            return
        }

        self.geocoderHandler.geocodeAddressString("\(location.name), \(location.additionalName)") { places, error in
            guard let places = places, error == nil else {
                return
            }

            self.currentLocation = places.compactMap({ place in
                return Location(name: location.name, additionalName: location.additionalName, description: location.description, coordinates: place.location?.coordinate)
            }).first!
            self._knownLocations.insert(self.currentLocation)
        }
    }
    
    func findLocation(address: String) {
        self.geocoderHandler.geocodeAddressString(address) { places, error in
            guard let places = places, error == nil else {
                return
            }

            self.currentLocation = places.compactMap({ place in
                return Location(name: address, additionalName: "", description: "", coordinates: place.location?.coordinate)
            }).first!
        }
    }

    func loadFromLocalStorage() -> Set<Location> {
        let decoder = JSONDecoder()

        do {
            let storedLocations = UserDefaults.standard.string(forKey: "knownLocations")
            if storedLocations != nil {
                return try decoder.decode(Set<Location>.self, from: storedLocations!.data(using: .utf8)!)
            }
        } catch {
            print("Error decoding array of structs: \(error)")
        }
        return []
    }

    func storeLocalStorage() {
        let encoder = JSONEncoder()

        do {
            let jsonData = try encoder.encode(self._knownLocations)
            UserDefaults.standard.set(String(data: jsonData, encoding: .utf8), forKey: "knownLocations")
        } catch {
            print("Error encoding array of structs: \(error)")
        }
    }
}
