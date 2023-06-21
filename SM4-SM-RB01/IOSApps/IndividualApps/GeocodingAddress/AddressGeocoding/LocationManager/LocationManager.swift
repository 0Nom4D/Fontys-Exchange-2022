//
//  LocationManager.swift
//  AddressGeocoding
//
//  Created by Nom4D on 27/03/2023.
//

import Foundation
import CoreLocation
import MapKit

class LocationManager: NSObject, ObservableObject {
    @Published var region = MKCoordinateRegion(
        center: CLLocationCoordinate2D(latitude: 34.011_286, longitude: -116.166_868),
        span: MKCoordinateSpan(latitudeDelta: 1.0, longitudeDelta: 1.0)
    )
    @Published var location: CLLocationCoordinate2D? = CLLocationCoordinate2D(latitude: 34.011_286, longitude: -116.166_868)

    private var startupLocation = CLLocationCoordinate2D(latitude: 34.011_286, longitude: -116.166_868)
    private let locationManager = CLLocationManager()

    private var isFirst: Bool = true

    override init() {
        super.init()
        locationManager.desiredAccuracy = kCLLocationAccuracyBest
        locationManager.distanceFilter = kCLDistanceFilterNone
        locationManager.requestAlwaysAuthorization()
        locationManager.startUpdatingLocation()
        locationManager.delegate = self
    }

    func getLocation() {
        switch locationManager.authorizationStatus {
            case .notDetermined, .denied, .restricted:
                region.center = startupLocation
            case .authorizedWhenInUse, .authorizedAlways:
                region.center = location!
            default:
                break
        }
    }
}

extension LocationManager: CLLocationManagerDelegate {
    func locationManager(_ manager: CLLocationManager, didUpdateLocations locations: [CLLocation]) {
        guard let location = locations.last else { return }
        self.location = location.coordinate

        if self.isFirst {
            self.getLocation()
            self.isFirst = false
        }
    }
}
